PDFLATEX = /usr/local/bin/pdflatex
PDFLATEXFLAGS = --interaction errorstopmode

all: pdf

pdf: exercises-1.pdf exercises-2.pdf exercises-3.pdf exercises-4.pdf exercises-5.pdf exercises-6.pdf exercises-7.pdf exercises-8.pdf exercises-9.pdf exercises-10.pdf exercises-11.pdf

%.pdf: %.tex
	$(PDFLATEX) $(PDFLATEXFLAGS) $< && $(PDFLATEX) $(PDFLATEXFLAGS) $<

clean:
	rm -f *.aux *.pdf *.log *.toc
