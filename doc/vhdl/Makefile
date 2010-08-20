EXAMPLES=fold_orig.tex fold_il.tex compteur.tex alloc.tex compteur2_init.tex \
	compteur2_sched.tex compteur2_vhdl.tex al2_init.tex al2_sched.tex al2_vhdl.tex

.PHONY:	all clean heptc

all:	rapport.pdf

heptc:
	cd ../../compiler ; ocamlbuild -j 0 heptc.byte ; \
		cp heptc.byte ../doc/vhdl/heptc ; cd ../doc/vhdl

%_vhdl:	%.ept
	heptc.byte -target vhdl $<
	rm -rf $(dir $<)/$(notdir $@)
	mv $(notdir $@) $(dir $<)

gencod.zip:	rapport.pdf heptc $(patsubst %.ept,%_vhdl,$(wildcard exs/*.ept))
	zip -r $@ $^

clean:
	rm -f $(EXAMPLES) archi.pdf pygments.tex archi.pdf *.aux *.bbl *.blg *.log
	rm -f *.out *.toc *.epci

rapport.pdf: rapport.tex archi.pdf pygments.tex $(EXAMPLES)
	pdflatex $<
	bibtex $(basename $<)
	pdflatex $<
	pdflatex $<
	cp $@ ~/Dropbox/Public

%.eps:	%.svg
	inkscape --export-eps=$@ $^

%.pdf:	%.eps
	ps2pdf $^

pygments.tex:
	pygmentize -S colorful -f latex > $@

%.tex:	%.ept
	pygmentize -o $@ $<

%.tex:	%.vhd
	pygmentize -o $@ $<

%.tex:	%.mls
	pygmentize -o $@ $<
