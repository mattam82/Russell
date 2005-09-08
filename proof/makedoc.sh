#/bin/bash
SOURCES=`cat .sources`

coqdoc -g --toc -d html -R . CCP --html ${SOURCES} 
