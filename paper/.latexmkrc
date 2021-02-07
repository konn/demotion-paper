#!/usr/bin/env perl
# $latex = 'xelatex -shell-escape -file-line-error -interaction=nonstopmode -halt-on-error -synctex=1';
# $pdflatex = 'xelatex -shell-escape -file-line-error -interaction=nonstopmode -halt-on-error -synctex=1';
$pdflatex = "lualatex %O -shell-escape -file-line-error -interaction=nonstopmode -halt-on-error -synctex=1 %S";
$lualatex = "lualatex %O -shell-escape -file-line-error -interaction=nonstopmode -halt-on-error -synctex=1 %S";
$latex = "lualatex %O -shell-escape -file-line-error -interaction=nonstopmode -halt-on-error -synctex=1 %S";
$bibtex           = 'pbibtex';
$biber            = 'biber --bblencoding=utf8 -u -U --output_safechars';
$dvipdf           = 'dvipdfmx %O -o %D %S';
$xelatex          = 'xelatex %O -shell-escape -file-line-error -interaction=nonstopmode -halt-on-error -synctex=1 %S';
$makeindex        = 'mendex %O -o %D %S';
$max_repeat       = 5;
$pdf_mode         = 1; # generates pdf via pdflatex (XeLaTeX).
# $pdf_mode	  = 3; # generates pdf via dvipdfmx

# Prevent latexmk from removing PDF after typeset.
# This enables Skim to chase the update in PDF automatically.
$pvc_view_file_via_temporary = 0;

# Use Skim as a previewer
$pdf_previewer    = "open -ga /Applications/Skim.app";
