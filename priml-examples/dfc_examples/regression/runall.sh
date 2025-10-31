#!/bin/sh

for file in *.prm
do
    echo -n "$file\t"
    time --quiet -f "%x\t%e" ../../../primlc $file out > /dev/null
done
