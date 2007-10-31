PDFLATEX = /usr/bin/pdflatex
PDFLATEXFLAGS = --interaction errorstopmode
PDFVIEW = /usr/bin/evince

all: pdf

preview: bachelor-project.pdf
	$(PDFVIEW) bachelor-project.pdf &

pdf: bachelor-project.pdf

%.pdf: %.tex
	$(PDFLATEX) $(PDFLATEXFLAGS) $< && $(PDFLATEX) $(PDFLATEXFLAGS) $<

clean:
	rm -f *.aux *.pdf *.log *.toc
