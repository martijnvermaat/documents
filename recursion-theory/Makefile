PDFLATEX = /usr/bin/pdflatex
PDFLATEXFLAGS = --interaction errorstopmode

all: pdf

pdf: exercises-1.pdf exercises-2.pdf exercises-3.pdf exercises-4.pdf

%.pdf: %.tex
	$(PDFLATEX) $(PDFLATEXFLAGS) $< && $(PDFLATEX) $(PDFLATEXFLAGS) $<

clean:
	rm -f *.aux *.pdf *.log *.toc
