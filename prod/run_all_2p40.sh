#!/bin/bash
# 23素数それぞれで [1, 2^40) を本番モードで回す。q ごとに log を分ける。終了コードを q ごとに記録する。
cd /w || exit 1
P=prod/verify_3xq_prod
: > prod/all_2p40_summary.txt
while IFS=$'\t' read -r q cms rest; do
  [ "$q" = -1 ] && continue
  s=$(date +%s)
  $P "$q" "$cms" 1 1099511627776 0 22 10 16 500 prod/q${q}_2p40.log > /dev/null 2> prod/q${q}_2p40.err; e=$?
  t=$(( $(date +%s) - s ))
  echo "q=$q exit=$e wall=${t}s $(grep -o 'chunks=[^|]*' prod/q${q}_2p40.log | tail -1) $(grep -o 'maxsteps=[0-9]* at n=[0-9]*' prod/q${q}_2p40.log | tail -1)" >> prod/all_2p40_summary.txt
done < cycles.txt
echo "== all done" >> prod/all_2p40_summary.txt
