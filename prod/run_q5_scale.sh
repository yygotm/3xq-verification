#!/bin/bash
# q=5 で N を上げたときの所要時間を測る（[2^40, 2^44) と [2^44, 2^48)）。区画は 2^40 の実行と同じ粒度にする。
cd /w || exit 1
P=prod/verify_3xq_prod
: > prod/q5_scale_summary.txt
for r in "1099511627776 17592186044416 26" "17592186044416 281474976710656 30"; do
  set -- $r
  s=$(date +%s)
  $P 5 1,5,19,23,187,347 $1 $2 0 $3 10 16 500 prod/q5_scale_$1_$2.log > /dev/null 2> prod/q5_scale_$1_$2.err; e=$?
  t=$(( $(date +%s) - s ))
  echo "[$1,$2) F=$3 exit=$e wall=${t}s $(grep -o 'chunks=[^|]*' prod/q5_scale_$1_$2.log | tail -1)" >> prod/q5_scale_summary.txt
done
echo "== done" >> prod/q5_scale_summary.txt
