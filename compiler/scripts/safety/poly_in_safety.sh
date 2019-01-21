#!/bin/sh
make;

(echo "poly1305 in: started";
 ./jasminc.native -debug -relational "len" -pointers "in" examples/safety/libjc/poly1305.jazz 2> safety_res/poly1305.in.res;
 echo "poly1305 in: done") &

(echo "poly1305le in: started";
 ./jasminc.native -debug -relational "len" -pointers "in" examples/safety/libjc/poly1305le.jazz 2> safety_res/poly1305le.in.res;
 echo "poly1305le in: done") &

(echo "poly1305ge in: started";
 ./jasminc.native -debug -relational "len" -pointers "in" examples/safety/libjc/poly1305ge.jazz 2> safety_res/poly1305ge.in.res;
 echo "poly1305ge in: done") &

wait;
echo "all tasks done";
