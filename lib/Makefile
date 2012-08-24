include ../config

STDLIB_INTERFACES=do.epi image.epi iostream.epi math_utils.epi pervasives.epi time.epi
STDLIB_OBJS=$(STDLIB_INTERFACES:.epi=.epci)

C_DIR=c

.SUFFIXES: .epi .epci

.epi.epci: pervasives.epci
	../compiler/$(COMPILER).$(TARGET) $<

.PHONY: all install clean

all: pervasives.epci $(STDLIB_OBJS)
	(cd $(C_DIR); $(MAKE) all)

pervasives.epci: pervasives.epi
	../compiler/$(COMPILER).$(TARGET) -nopervasives pervasives.epi

install: all
	$(INSTALL) -d $(INSTALL_LIBDIR)
	$(INSTALL) $(STDLIB_OBJS) $(STDLIB_INTERFACE) $(INSTALL_LIBDIR)
	$(INSTALL) -d $(INSTALL_LIBDIR)/$(C_DIR)
	(cd c/; $(MAKE) install)

clean:
	rm -f $(STDLIB_OBJS)
	(cd $(C_DIR); $(MAKE) clean)
