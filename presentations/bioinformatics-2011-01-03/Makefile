# Generate PDF from LaTeX and BibTeX source.
#
# There are some hacks in here to work with LaTeX compilation, I'll try
# to document them with comments :)
#
# Martijn Vermaat, martijn@vermaat.name

# Configuration
SLIDES = slides
PDFLATEX = /usr/bin/pdflatex
PDFLATEXFLAGS = -halt-on-error -interaction errorstopmode
PDFVIEW = /usr/bin/evince

# Just create the PDF!
all: pdf

# Create the files
pdf: $(SLIDES).pdf

# For the PDF, we need a .tex LaTeX source. Actually, we also need a .bbl
# BibTeX database, but we don't want to regenerate that on every .tex change.
# We compile the file twice to make sure all references are okay.
%.pdf: %.tex
	$(PDFLATEX) $(PDFLATEXFLAGS) $<
	while egrep -q -s 'Rerun (LaTeX|to get cross-references right)' $*.log ;\
	    do \
	        $(PDFLATEX) $(PDFLATEXFLAGS) $< ;\
	    done

# Please make sure we don't kill any sources...
clean:
	rm -f *.aux *.pdf *.log *.toc *.out *.bbl *.blg *.nav *.snm *.vrb
