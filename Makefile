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

guile-build-%/meta/guile: guile-src-%
	$(ENV) mkdir guile-build-$*
	$(ENV) bash -c 'cd guile-build-$* && ../$</configure'
	$(ENV) make -C guile-build-$* $(MAKEFLAGS)

variants=online-cse no-online-cse
guile_src_dirs=$(foreach variant,$(variants),guile-src-$(variant))
guile_build_dirs=$(foreach variant,$(variants),guile-build-$(variant))
guiles=$(foreach build_dir,$(guile_build_dirs),$(build_dir)/meta/guile)
guile=$(firstword $(guiles))

code-size-comparison.csv: $(guiles) compare-code-sizes.scm
	$(ENV) $(guile) compare-code-sizes.scm \
	   guile-build-no-online-cse/module guile-build-online-cse/module > $@

sizes=256 512 1024 2048 4096 8192 16384 32768 65536 131072
tests=$(foreach size,$(sizes),test-$(size).scm)
test-%.scm: make-test.scm $(guile)
	$(ENV) $(guile) make-test.scm $* > $@

tests: $(tests)

# time to compile test-N.scm for each; proxy for memory
# expected run-time for dispatching N/2

clean:
	rm -f guile-3.0.5.tar.lz
	rm -rf $(guile_src_dirs) $(guile_build_dirs)
	rm -f code-size-comparison.csv $(tests)

.PRECIOUS: guile-src-% guile-bin-%
