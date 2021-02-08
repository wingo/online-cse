HOST_GUIX ?= guix
GUIX ?= $(HOST_GUIX) time-machine -C channels.scm --

ENV ?= $(GUIX) environment --pure -m manifest.scm --
J ?= -j4

guile-3.0.5.tar.lz:
	$(ENV) wget https://ftp.gnu.org/pub/gnu/guile/guile-3.0.5.tar.lz
	$(ENV) sha256sum -c guile-3.0.5.tar.lz.checksum

guile-src-%: guile-3.0.5.tar.lz
	$(ENV) bash -c 'mkdir $@-tmp && cd $@-tmp && tar xvf ../$< && mv $(subst .tar.lz,,$<) ../$@'
	$(ENV) rmdir $@-tmp
	$(ENV) bash -c 'if test -f $*.patch; then cd $@ && patch -u -p1 < ../$*.patch; fi'

guile-bin-%: guile-src-%
	$(ENV) bash -c 'cd $< && ./configure'
	$(ENV) make -C $< $(MAKEFLAGS)
	$(ENV) rm -f $@
	$(ENV) ln -s $</meta/guile $@

code-size-comparison.csv: guile-bin-no-online-cse guile-bin-online-cse compare-code-sizes.scm
	$(ENV) ./guile-bin-online-cse compare-code-sizes.scm \
	   guile-src-no-online-cse/module guile-src-online-cse/module > $@

sizes=256 512 1024 2048 4096 8192 16384 32768 65536 131072
tests=$(foreach size,$(sizes),test-$(size).scm)
test-%.scm: make-test.scm guile-bin-online-cse
	$(ENV) ./guile-bin-online-cse make-test.scm $* > $@

tests: $(tests)

# time to compile test-N.scm for each; proxy for memory
# expected run-time for dispatching N/2

clean:
	rm -rf guile-src-online-cse guile-src-no-online-cse
	rm -f guile-3.0.5.tar.lz
	rm -f guile-bin-online-cse guile-bin-no-online-cse
	rm -f code-size-comparison.csv $(tests)

.PRECIOUS: guile-src-% guile-bin-%
