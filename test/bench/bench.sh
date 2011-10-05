#!/bin/bash

run_bench() {
    HFLAGS="$1"
    echo "HFLAGS := $HFLAGS" > Makefile.config
    make -j clean all > /dev/null
    for bin in *.out
    do
        echo "Timing $bin, options = \"$HFLAGS\""
        time ./$bin data
    done
}

run_bench ""
run_bench "-tomato"
run_bench "-memalloc"
run_bench "-tomato -memalloc"