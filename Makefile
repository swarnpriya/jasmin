#! -*- Makefile -*-

# --------------------------------------------------------------------
DISTDIR := jasmin
UNAME_S := $(shell uname -s)
SED     ?= sed

# --------------------------------------------------------------------
.PHONY: all check clean dist distcheck

all:
	$(MAKE) -C proofs all
	$(MAKE) -C compiler CIL
	$(MAKE) -C compiler all

check:
	$(MAKE) -C eclib check

clean:
	$(MAKE) -C proofs clean
	$(MAKE) -C compiler clean

dist:
	rm -rf jasmin jasmin.tar.gz
	./scripts/distribution $(DISTDIR) MANIFEST
	rm -rf jasmin/proofs/logic
	if [ -x scripts/anonymize ]; then SED=$(SED) scripts/anonymize; fi
	$(SED) -i -e "/logic/d" jasmin/proofs/_CoqProject
	tar -czf jasmin.tar.gz --owner=0 --group=0 jasmin && rm -rf jasmin

distcheck: dist
	tar -xof $(DISTDIR).tar.gz
	set -x; \
	     $(MAKE) -C $(DISTDIR) \
	  && $(MAKE) -C $(DISTDIR) dist \
	  && mkdir $(DISTDIR)/dist1 $(DISTDIR)/dist2 \
	  && ( cd $(DISTDIR)/dist1 && tar -xof ../$(DISTDIR).tar.gz ) \
	  && ( cd $(DISTDIR)/dist2 && tar -xof ../../$(DISTDIR).tar.gz ) \
	  && diff -rq $(DISTDIR)/dist1 $(DISTDIR)/dist2 \
	  || exit 1
	rm -rf $(DISTDIR)
	@echo "$(DISTDIR) is ready for distribution" | \
	  $(SED) -e 1h -e 1s/./=/g -e 1p -e 1x -e '$$p' -e '$$x'
