#!/bin/sh
make;

(echo "poly1305 out: started";
 ./jasminc.native -debug -relational "len" -pointers "out" examples/safety/libjc/poly1305.jazz 2> safety_res/poly1305.out.res;
 echo "poly1305 out: done") &

(echo "poly1305le out: started";
 ./jasminc.native -debug -relational "len" -pointers "out" examples/safety/libjc/poly1305le.jazz 2> safety_res/poly1305le.out.res;
 echo "poly1305le out: done") &

(echo "poly1305ge out: started";
 ./jasminc.native -debug -relational "len" -pointers "out" examples/safety/libjc/poly1305ge.jazz 2> safety_res/poly1305ge.out.res;
 echo "poly1305ge out: done") &

wait;
echo "all tasks done";
