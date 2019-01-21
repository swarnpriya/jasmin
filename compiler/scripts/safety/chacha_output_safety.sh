#!/bin/sh
make;

(echo "chacha20 output: started";
 ./jasminc.native -debug -relational "len" -pointers "output" examples/safety/libjc/chacha20.jazz 2> safety_res/chacha20.output.res;
 echo "chacha20 output: done") &

(echo "chacha20le output: started";
 ./jasminc.native -debug -relational "len" -pointers "output" examples/safety/libjc/chachale.jazz 2> safety_res/chachale.output.res;
 echo "chacha20le output: done") &

(echo "chacha20ge output: started";
 ./jasminc.native -debug -relational "len" -pointers "output" examples/safety/libjc/chachage.jazz 2> safety_res/chachage.output.res;
 echo "chacha20ge output: done") &

wait;
echo "all tasks done";
