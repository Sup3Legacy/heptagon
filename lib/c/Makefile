include ../../config
ASYNC_HEADERS= async/async_fun.h async/async_macros.h async/async_node.h async/futures.h async/spsc_bounded_fifo.h async/stock.h async/utils.h
HEADERS=pervasives.h async.h do.h htime.h
SRC=do.cpp htime.cpp

COMPILED_HEADERS=$(HEADERS:.h=.h.gch)

OBJS=$(SRC:.cpp=.o)

C_STDLIB_STATIC=$(STDLIB_NAME).a

%.h.gch: %.h
	$(CXX) $(CXXFLAGS) $<


.PHONY: all

all: compiled_headers $(C_STDLIB_STATIC)

compiled_headers: $(COMPILED_HEADERS)

static_lib: $(C_STDLIB_STATIC)

$(C_STDLIB_STATIC): $(OBJS)
	ar -r $(C_STDLIB_STATIC) $(OBJS)

async.h.gch: $(ASYNC_HEADERS)
	$(CXX) $(CXXFLAGS) async.h

install: all
	$(INSTALL) -d $(INSTALL_LIBDIR)
	$(INSTALL) $(C_STDLIB_STATIC) $(INSTALL_LIBDIR)/$(C_STDLIB_STATIC)

clean :
	rm -f $(OBJS)
	rm -f $(COMPILED_HEADERS)

clean_all: clean
	rm -f $(C_STDLIB_STATIC)
