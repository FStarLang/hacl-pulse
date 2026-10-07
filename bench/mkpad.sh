#!/bin/bash
# $1 = number of 1-byte padding functions
n=$1
if [ "$n" -eq 0 ]; then : > pad_$n.c; else printf 'void pad_%s(void){}\n' $(seq 1 $n) > pad_$n.c; fi
${BENCH_CC:-gcc} -std=c11 -O3 -falign-functions=1 -c pad_$n.c -o pad_$n.o
