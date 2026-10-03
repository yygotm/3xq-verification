#!/bin/bash
# コンテナ内で実行する試験（/w = このリポジトリ、/m = 3xm1 を読み取り専用）。結果は logs/ に残し、要約を標準出力に出す。
# 検証プログラムは失敗時に終了コード 2 を返すので、set -e は使わず、終了コードを個別に記録する。
cd /w || exit 1
mkdir -p logs
H=$(md5sum verify_3xq.c | cut -c1-12)                                 # ソースの版を tag に入れる（本番のビルドでも同じ -D を渡すこと）
CFLAGS=(-O3 -march=native -fopenmp -Wall -Wextra "-DSRC_HASH=\"$H\"")
if ! gcc "${CFLAGS[@]}" -o verify_3xq verify_3xq.c -lm 2> logs/build_warnings.txt; then cat logs/build_warnings.txt; exit 1; fi
echo "== build warnings: $(wc -l < logs/build_warnings.txt) lines"; head -20 logs/build_warnings.txt
gcc -O3 -march=native -fopenmp -Wall -o verify2_ref /m/verify2.c -lm || exit 1
md5sum /m/verify2.c verify_3xq.c > logs/md5.txt

echo "== cycle minima (brute force, n < 200000)"
python3 enum_cycles.py 200000 > cycles.txt || exit 1
cut -f1,2 cycles.txt

strip() { sed -E 's/ time=[^ ]+ rate=[^ ]+//'; }

echo "== regression q=-1 against verify2 (3x-1)"
# LO=1 では n <= CEMAX=136 の扱い（trace_ce）が移植元と違い、stats が一致しないことがある（正確性レビュー [低3]）。LO=137 の行で丸ごと比べる
for args in "1 4194304 2 10 10 2" "1 4194304 0 10 10 2" "137 4194304 0 10 10 2" "137 4194304 1 10 10 2" "1 20971520 1 16 10 2" "1099511627776 1099515822080 2 16 10 2" "35184372088832 35184388866048 2 12 10 16"; do
  ./verify2_ref $args > logs/ref.txt 2> logs/ref.err; rr=$?
  ./verify_3xq -1 1,5,17 $args > logs/new.txt 2> logs/new.err; rn=$?
  if diff <(strip < logs/ref.txt) <(strip < logs/new.txt) > /dev/null && [ $rr = $rn ] && [ "$(grep SKIP_T logs/ref.err)" = "$(grep SKIP_T logs/new.err)" ]; then
    echo "SAME  [$args] exit=$rn $(grep -o 'accounted.*' logs/new.txt | head -1)"
  else
    echo "DIFF  [$args] exit ref=$rr new=$rn"; strip < logs/ref.txt; strip < logs/new.txt; grep SKIP_T logs/ref.err logs/new.err
  fi
done

echo "== 3x+q selfcheck (mode 2) A=[1,2^22) B=[2^40,2^40+2^20), exact (mode 1) C=[1,2^20), production path (mode 0, leaf_fast) D=[2^40,2^40+2^20)"
summ() { echo "$(grep -o 'fails=[0-9]*' "$1") $(grep -o 'OK$\|MISMATCH' "$1") $(grep -o 'selfcheck_bad=[0-9]*' "$1")"; }
while IFS=$'\t' read -r q cms rest; do
  [ "$q" = -1 ] && continue
  [ -z "$cms" ] && { echo "q=$q: empty CMINS line"; continue; }
  ./verify_3xq "$q" "$cms" 1 4194304 2 10 10 2 > logs/q${q}_a.txt 2> logs/q${q}_a.err; ea=$?
  ./verify_3xq "$q" "$cms" 1099511627776 1099512676352 2 16 10 2 > logs/q${q}_b.txt 2> logs/q${q}_b.err; eb=$?
  ./verify_3xq "$q" "$cms" 1 1048576 1 16 10 2 > logs/q${q}_c.txt 2> logs/q${q}_c.err; ec=$?
  ./verify_3xq "$q" "$cms" 1099511627776 1099512676352 0 16 10 2 > logs/q${q}_d.txt 2> logs/q${q}_d.err; ed=$?
  echo "q=$q exits=$ea/$eb/$ec/$ed | A: $(summ logs/q${q}_a.txt) | B: $(summ logs/q${q}_b.txt) | C: $(summ logs/q${q}_c.txt) | D: $(summ logs/q${q}_d.txt) | $(grep -oh 'SKIP_T=[0-9]*\|CEMAX=[0-9]*' logs/q${q}_a.err | tr '\n' ' ')"
  grep -h FAIL logs/q${q}_*.err | head -3
done < cycles.txt

echo "== negative: q=5 without the cycle of 19 must FAIL (expect exit 2)"
./verify_3xq 5 1,5,23,187,347 1 1048576 0 10 10 2 > logs/neg.txt 2> logs/neg.err; echo "exit=$? FAIL lines=$(grep -c FAIL logs/neg.err)"
echo "== BENCH_STRIDE must not exit 0 (expect exit 4)"
BENCH_STRIDE=8 ./verify_3xq 5 1,5,19,23,187,347 1 1048576 0 10 10 2 > /dev/null 2>&1; echo "exit=$?"
echo "== checkpoint: resume accepts only DONE lines from the same build"
rm -f logs/ckpt.log
./verify_3xq 5 1,5,19,23,187,347 1 4194304 0 10 10 2 4 logs/ckpt.log > /dev/null 2> logs/ckpt1.err; e1=$?
./verify_3xq 5 1,5,19,23,187,347 1 4194304 0 10 10 2 4 logs/ckpt.log > /dev/null 2>&1; e2=$?
gcc "${CFLAGS[@]}" -DJK=8 -o verify_3xq_jk8 verify_3xq.c -lm || exit 1
./verify_3xq_jk8 5 1,5,19,23,187,347 1 4194304 0 10 10 2 4 logs/ckpt.log > /dev/null 2>&1; e3=$?
fr=$(grep -o 'front=[0-9]*' logs/ckpt1.err | cut -d= -f2); nch=$(( (fr + 3) / 4 ))
echo "exits=$e1/$e2/$e3 (expect 0/0/0) DONE=$(grep -c '^DONE' logs/ckpt.log) (expect $((2 * nch)): jk10 once + jk8 once) ALLDONE=$(grep -c '^ALLDONE' logs/ckpt.log) (expect 3)"
echo "== done"
