#/bin/bash
SOURCES=`find . -name "*.v"`
echo ${SOURCES}
coqdoc --coqlib_path "`coqc -where`" --multi-index --glob-from globals.dump -g -l -t "Russell metatheoretic study" --toc -d html --html ${SOURCES} 
