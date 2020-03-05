#  Copyright 2006 INRIA

REFFILES = reference.tex macros.tex \
	   install.tex options.tex input-zen.tex input-tptp.tex \
	   input-coq.tex messages.tex

include ../.config_var

# Only try to build doc if source files are present.
doc: reference.pdf

reference.pdf: ${REFFILES}
	pdflatex reference.tex
	pdflatex reference.tex

.PHONY: logo
logo: zenon-logo.png zenon-logo-small.png

zenon-logo.png: zenon-logo.ps
	${GS} -q -sDEVICE=png16m -sOutputFile=zenon-logo.png -r720 -g2400x800 \
	   -dNOPAUSE -dBATCH zenon-logo.ps

# "convert" is part of ImageMagick
zenon-logo-small.png: zenon-logo.png
	${CONVERT} zenon-logo.png -resize 10% zenon-logo-small.png

clean:
	rm -f *.aux *.dvi *.log *.toc
	rm -f $(OBJS) zenon-logo.png zenon-logo-small.png
