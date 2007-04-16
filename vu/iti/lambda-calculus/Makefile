PDFLATEX = /usr/bin/pdflatex
PDFLATEXFLAGS = --interaction errorstopmode
PDFVIEW = /usr/bin/evince

all: pdf

preview: uitwerkingen.pdf
	$(PDFVIEW) uitwerkingen.pdf &

pdf: uitwerkingen.pdf

%.pdf: %.tex
	$(PDFLATEX) $(PDFLATEXFLAGS) $< && $(PDFLATEX) $(PDFLATEXFLAGS) $<

clean:
	rm -f *.aux *.pdf *.log *.toc
