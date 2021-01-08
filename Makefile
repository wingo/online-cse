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
	$(ENV) make -C $< $(J)
	$(ENV) ln -s $</meta/guile $@

foo:
	$(GUIX) build guile

.PHONY: foo
