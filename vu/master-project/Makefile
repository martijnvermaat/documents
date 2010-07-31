# Generate PDF from LaTeX and BibTeX source.
#
# There are some hacks in here to work with LaTeX compilation, I'll try
# to document them with comments :)
#
# Martijn Vermaat, martijn@vermaat.name

# Configuration
THESIS = thesis
THESISDEPS = vu.cls abbrevs.tex discussion.tex glossary.tex implementation.tex introduction.tex preface.tex rewriting.tex unwo.tex figures/tree-ordinal.tikz figures/predecessor.tikz
SLIDES = slides
SLIDESDEPS = abbrevs.tex figures/predecessor.tikz
PDFLATEX = /usr/bin/pdflatex
PDFLATEXFLAGS = -halt-on-error -interaction errorstopmode
BIBTEX = /usr/bin/bibtex
PDFVIEW = /usr/bin/evince

# Just create the PDF!
all: pdf

# Create PDF and have a look at it
preview: $(THESIS).pdf
	$(PDFVIEW) $< &

# Compile BibTeX source file (run this when citations or .bib file change)
bibtex: $(THESIS).bbl

# Create the files
pdf: $(THESIS).pdf $(SLIDES).pdf

# The thesis depends on these files
$(THESIS).pdf: $(THESISDEPS)

# The slides depend on these files
$(SLIDES).pdf: $(SLIDESDEPS)

# For the PDF, we need a .tex LaTeX source. Actually, we also need a .bbl
# BibTeX database, but we don't want to regenerate that on every .tex change.
# We compile the file twice to make sure all references are okay.
%.pdf: %.tex
	$(PDFLATEX) $(PDFLATEXFLAGS) $<
	while egrep -q -s 'Rerun (LaTeX|to get cross-references right)' $*.log ;\
	    do \
	        $(PDFLATEX) $(PDFLATEXFLAGS) $< ;\
	    done
	$(PDFLATEX) $(PDFLATEXFLAGS) $< # With ntheorem, another run is needed

# For the .bbl BibTeX database we need the .bib BibTeX source and .tex LaTeX
# source.
# Afterwards, we remove the resulting PDF, because we require some additional
# compilation passes that are done by the %.pdf rule.
%.bbl: %.bib %.tex
	$(PDFLATEX) $(PDFLATEXFLAGS) $*
	$(BIBTEX) $*
	$(PDFLATEX) $(PDFLATEXFLAGS) $*
	while egrep -q -s 'Rerun (LaTeX|to get cross-references right)' $*.log ;\
	    do \
	        $(PDFLATEX) $(PDFLATEXFLAGS) $* ;\
	    done
	/bin/rm $*.pdf

# Please make sure we don't kill any sources...
clean:
	rm -f *.aux *.pdf *.log *.toc *.out *.bbl *.blg *.nav *.snm *.vrb
