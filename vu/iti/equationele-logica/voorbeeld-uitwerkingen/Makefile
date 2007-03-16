PDFLATEX = /usr/local/bin/pdflatex
PDFLATEXFLAGS = --interaction errorstopmode

all: pdf

pdf: uitwerkingen.pdf

%.pdf: %.tex
	$(PDFLATEX) $(PDFLATEXFLAGS) $<

clean:
	rm -f *.aux *.pdf *.log
