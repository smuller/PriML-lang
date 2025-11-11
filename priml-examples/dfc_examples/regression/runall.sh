#!/bin/sh

for file in *.prm
do
    echo -n "$file\t"
    time --quiet -o /dev/tty -f "%x\t%e" ../../../primlc $file out > /dev/null 2> /dev/null
done
