#!/bin/sh
generate() {
	coqdoc --latex --body-only $1.v > $1.tex 
}

generate subtac-euclid
generate lt_ge_dec-proof
generate lt_ge_dec-tactic
