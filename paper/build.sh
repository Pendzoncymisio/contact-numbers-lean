#!/bin/sh
# pdflatex, matching arXiv's default engine.
set -e
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode contact-numbers.tex
bibtex contact-numbers
pdflatex -interaction=nonstopmode contact-numbers.tex
pdflatex -interaction=nonstopmode contact-numbers.tex
