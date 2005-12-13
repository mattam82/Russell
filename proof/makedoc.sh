#/bin/bash
SOURCES=`find . -name "*.v"`
echo ${SOURCES}
coqdoc -g --toc -d html --html ${SOURCES} 
