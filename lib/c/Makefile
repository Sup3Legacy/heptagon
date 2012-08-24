include ../../config

HEADERS=pervasives.h async.h do.h
SRC=do.cpp

COMPILED_HEADERS=$(HEADERS:.h=.h.gch)

OBJS=$(SRC:.cpp=.o)

C_STDLIB_STATIC=$(STDLIB_NAME).a

.SUFFIXES: .gch

%.gch: %
	$(CXX) $(CXXFLAGS) $< 

.PHONY: all

all: compiled_headers $(C_STDLIB_STATIC)

compiled_headers: $(COMPILED_HEADERS)

static_lib: $(C_STDLIB_STATIC)

$(C_STDLIB_STATIC): $(OBJS)
	ar -r $(C_STDLIB_STATIC) $(OBJS)


install: all
	$(INSTALL) -d $(INSTALL_LIBDIR)
	$(INSTALL) $(C_STDLIB_STATIC) $(INSTALL_LIBDIR)/$(C_STDLIB_STATIC)

clean :
	rm -f $(OBJS)
	rm -f $(COMPILED_HEADERS)

clean_all: clean
	rm -f $(C_STDLIB_STATIC)
