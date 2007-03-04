#!/bin/sh
COQDOC=coqdoc
DIR=.
COQDOCOPTS="--body-only -g --latex -d ${DIR}"

SOURCES="euclid.v"

for src in ${SOURCES}
  do
  ${COQDOC} ${COQDOCOPTS} ${src}
  sed -e "s/|/\\\coqor /g" -i ${DIR}/${src/.v/.tex}
  sed -e "s/Coq\(.\\|,\\| \)/\\\Coq\1/g" -i ${DIR}/${src/.v/.tex}
  sed -e "s/Russell/\\\Russell/g" -i ${DIR}/${src/.v/.tex}
done
