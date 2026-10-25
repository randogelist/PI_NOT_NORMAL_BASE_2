.PHONY: all clean

all: pi_ct_preprint.pdf

pi_ct_preprint.pdf: pi_ct_preprint.tex
	mkdir -p .build
	pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory=.build pi_ct_preprint.tex
	pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory=.build pi_ct_preprint.tex
	cp .build/pi_ct_preprint.pdf pi_ct_preprint.pdf

clean:
	rm -rf .build
