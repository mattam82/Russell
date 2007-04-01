#!/bin/sh
if [ $# -eq 0 ]
then
	exit
fi

dvips -P pdf -ta4 $1.dvi -o tmp.ps
psnup -1 -W128mm -H96mm -pa4 tmp.ps $1.ps
rm tmp.ps

#pdfnup --paper a4paper --orient auto --noautoscale false --nup $1 --outfile slides-handout-$1.pdf slides-handout.pdf

#pdf90 slides-handout-$1.pdf
#pdftops -level3 -expand slides-handout-$1-rotated.pdf slides-handout-$1.ps
#rm -f slides-handout-{$1}*.pdf
