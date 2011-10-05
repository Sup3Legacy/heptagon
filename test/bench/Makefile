include Makefile.config

HEPTDIR := $(shell heptc -where)
CFLAGS := -std=c99 -I$(HEPTDIR)/c

.PHONY: all clean

all: shuffle.out

clean:
	rm -f *.{out,epci,mls}
	rm -rf *_c

%.out: %.ept main_%.c
	heptc.byte $(HFLAGS) -target c $<
	cp main_$(basename $<).c $(basename $<)_c
	cp Makefile* $(basename $<)_c
	make -C $(basename $<)_c $@
	cp $(basename $<)_c/$@ .

%.out: $(wildcard *.c)
	gcc $(CFLAGS) -o $@ $^

%.o:	%.c %.h
	gcc -c $(CFLAGS) $< -o $@
