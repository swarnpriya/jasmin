#!/bin/sh
make;

(echo "poly1305 in: started";
 ./jasminc.native -debug -relational "len" -pointers "in" examples/safety/libjc/poly1305.jazz 2> safety_res/poly1305.in.res;
 echo "poly1305 in: done") &

(echo "poly1305 out: started";
 ./jasminc.native -debug -relational "len" -pointers "out" examples/safety/libjc/poly1305.jazz 2> safety_res/poly1305.out.res;
 echo "poly1305 out: done") &

(echo "chacha20 output: done";
 ./jasminc.native -debug -relational "len" -pointers "output" examples/safety/libjc/chacha20.jazz 2> safety_res/chacha20.output.res;
 echo "chacha20 output: done") &

(echo "chacha20 plain: done";
 ./jasminc.native -debug -relational "len" -pointers "plain" examples/safety/libjc/chacha20.jazz 2> safety_res/chacha20.plain.res;
 echo "chacha20 plain: done") &

wait;
echo "all tasks done";
