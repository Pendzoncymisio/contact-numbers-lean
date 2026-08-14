# Built with pdflatex, to match arXiv's default engine. The Lean notation is
# mapped to math glyphs with \DeclareUnicodeCharacter, so no fontspec is needed.
#
# Note: on this system /etc/latexmkrc leaves $pdf_mode at its default of 0, i.e.
# DVI output and no PDF at all. Setting it here makes a bare `latexmk`, and any
# editor recipe that calls latexmk, produce the PDF with the right engine.
$pdf_mode = 1;          # 1 = pdflatex (arXiv default)
$postscript_mode = 0;
$dvi_mode = 0;
