HOST_GUIX ?= guix
GUIX ?= $(HOST_GUIX) time-machine -C channels.scm --

ENV ?= $(GUIX) environment --pure -m manifest.scm --
J ?= -j4

guile-3.0.5.tar.lz:
	$(ENV) wget https://ftp.gnu.org/pub/gnu/guile/guile-3.0.5.tar.lz
	$(ENV) sha256sum -c guile-3.0.5.tar.lz.checksum

guile-src-%: guile-3.0.5.tar.lz
	$(ENV) tar xvf guile-3.0.5.tar.lz
	$(ENV) mv guile-3.0.5 $@
	$(ENV) bash -c 'if test -f $*.patch; then cd $< && patch -u -p1 ../$*.patch; fi'

guile-bin-%: guile-src-%
	$(ENV) bash -c 'cd $< && ./configure'
	$(ENV) make -C $< $(MAKEFLAGS)
	$(ENV) rm -f $@
	$(ENV) ln -s $</meta/guile $@

code-size-comparison.csv: guile-bin-no-online-cse guile-bin-online-cse compare-code-sizes.scm
	$(ENV) ./guile-bin-online-cse compare-code-sizes.scm \
	   guile-src-no-online-cse/module guile-src-online-cse/module > $@

.PRECIOUS: guile-src-% guile-bin-%
