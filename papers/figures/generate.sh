#!/bin/sh

COQDOC=/home/sozeau/V8/bin/coqdoc

generate() {
	$COQDOC --latex --body-only $1.v > $1.tex 
}

generate subtac-euclid
generate subtac-euclid-tcc
generate lt_ge_dec-proof
generate lt_ge_dec-tactic
generate le_lt_dec-def
generate le_lt_dec-tactic
generate le_lt_dec-term
generate le_lt_dec-extterm
