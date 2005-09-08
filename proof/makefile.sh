#/bin/bash
SOURCES=`cat .sources`

coq_makefile -opt -R . CCP -o Makefile ${SOURCES} 
