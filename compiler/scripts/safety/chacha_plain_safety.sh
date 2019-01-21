#!/bin/sh
make;

(echo "chacha20 plain: started";
 ./jasminc.native -debug -relational "len" -pointers "plain" examples/safety/libjc/chacha20.jazz 2> safety_res/chacha20.plain.res;
 echo "chacha20 plain: done") &

(echo "chacha20le plain: started";
 ./jasminc.native -debug -relational "len" -pointers "plain" examples/safety/libjc/chachale.jazz 2> safety_res/chachale.plain.res;
 echo "chacha20le plain: done") &

(echo "chacha20ge plain: started";
 ./jasminc.native -debug -relational "len" -pointers "plain" examples/safety/libjc/chachage.jazz 2> safety_res/chachage.plain.res;
 echo "chacha20ge plain: done") &

wait;
echo "all tasks done";
