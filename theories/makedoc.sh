#/bin/bash
SOURCES=`grep .v Make`
echo ${SOURCES}
rm html/*
coqdoc --coqlib_path "`coqc -where`" --multi-index --glob-from globals.dump -g -l -t "Russell metatheoretic study" --toc -d html --html ${SOURCES} 
rm html/coqdoc.css
ln -s ~/research/publication/styles/coqdoc.css html
