#!/bin/bash
# 23素数それぞれで [2^40, 2^48) を本番モードで回す（[1, 2^40) は q ごとの q${q}_2p40.log で済み）。
# q=5 は [2^40,2^44) と [2^44,2^48) の計測で済んでいるので飛ばす。
# チェックポイント付き: 止めても同じ台本を流し直せば、済んだ区画を飛ばして続きから再開する。
cd /w || exit 1
P=prod/verify_3xq_prod
S=prod/all_2p48_summary.txt
echo "== start $(date -u '+%F') $(md5sum $P | cut -c1-12)" >> $S
while IFS=$'\t' read -r q cms rest; do
  [ "$q" = -1 ] && continue
  [ "$q" = 5 ] && continue
  L=prod/q${q}_2p40_2p48.log
  if grep -q '^ALLDONE' "$L" 2>/dev/null; then continue; fi
  s=$(date +%s)
  $P "$q" "$cms" 1099511627776 281474976710656 0 30 10 16 500 "$L" > /dev/null 2> prod/q${q}_2p40_2p48.err; e=$?
  t=$(( $(date +%s) - s ))
  echo "q=$q exit=$e wall=${t}s $(date -u '+%F') $(grep '^ALL' "$L" | tail -1 | grep -o 'chunks=[^|]*')" >> $S
  [ $e = 0 ] || { echo "q=$q FAILED (exit $e), stopping" >> $S; exit $e; }
done < cycles.txt
echo "== all done $(date -u '+%F')" >> $S
