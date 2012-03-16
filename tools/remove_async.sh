#!/bin/bash
sed -e 's/future //g' -e 's/async //g' -e 's/\!//g' < $1 > $2
