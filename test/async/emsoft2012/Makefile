
EPTS=utils.ept slow_fast.ept data_par.ept
EPIS=

DEP_utils=
DEP_slow_fast=utils.ept
DEP_data_par=utils.ept


BINS=data_par+main+c

C_FOLDERS=$(patsubst %.ept,%_c,$(EPTS))


HEPTGCC=$(CXX) $(CXXFLAGS) -I ~/W/heptagon/lib/c 
LIBDECADE=~/W/heptagon/lib/c/libdecades.a
HEPTC=weptc -O

.PHONY: all

all: $(BINS)




# Call with:
#   make <module>+<main>+c

include ../../../config

# Some macros from Nhat
define splitnth
$(word $1,$(subst $2, ,$3))
endef

# get module name from <module>+...
define getmodule
$(call splitnth,1,+,$1)
endef

#get main name from <module>+<main>+...
define getmain
$(call splitnth,2,+,$1)
endef



define getCDeps
$(patsubst %.ept,%_c,$(DEP_$(patsubst %.ept,%,$1)))
endef


# rule dependance template like t1.ept : t2.ept t3.ept ...
#define CDepTemplate
#$(i:.ept=_c): $(call getCDeps,$i)
#endef

# instanciate C dependances templates
#$(foreach i,$(EPTS),$(eval $(call CDepTemplate)))


%_c: %.ept
	$(HEPTC) $(HEPTCFLAGS) -target c -c $<

%.cpp: $(@D)

%.o: %.cpp
	$(HEPTGCC) $(patsubst %,-I ../%,$(call getCDeps,$<)) -c -o $@ $<



.PHONY:clean
clean:
	rm -rf $(C_FOLDERS)


.SECONDEXPANSION:

%+c: $$(call getmodule,$$*).ept $$(call getmodule,$$*)_c/$$(call getmodule,$$*).o $$(call getmodule,$$*)_c
	rm -rf $@
	$(HEPTC) $(HEPTCFLAGS) -target c -s $(call getmain,$@) $<
	cd $(call getmodule,$@)_c;\
	$(HEPTGCC) $(LIBDECADE) $(patsubst %,-I ../%,$(call getCDeps,$<)) $(patsubst %,../%/*.o,$(call getCDeps,$<)) *.o _main.cpp;\
	mv -f a.out ../$@

