# 3x+q 写像 T(x) = x/2（偶数）、(3x+q)/2（奇数）の巡回の最小元を、出発値 n < LIMIT の総当たりで列挙する。
# n の軌道が n より下がれば n は新しい巡回の最小元ではない。n に戻れば n が巡回の最小元（他の元は全て n より大きい）。
# 完全性はこの列挙では保証しない（verify_3xq が、列挙に無い最小元があれば FAIL で検出する）。
import sys

QS = [-1, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
CAP = 100000

def cycle_info(n, q):
    """n が巡回の最小元なら (長さ, 奇数の個数) を返す。そうでなければ None。
    n より下がらずに、n を含まない巡回へ下から入ることもある（q=5 の 3 → 7 → 13 → 22 → 11 → 19）。
    そのときは値の繰り返しで検出して None を返す。"""
    x, steps, odd, seen = n, 0, 0, {n}
    while True:
        if x & 1:
            x = (3 * x + q) >> 1; odd += 1
        else:
            x >>= 1
        steps += 1
        if x < n:
            return None
        if x == n:
            return steps, odd
        if x in seen:
            return None                      # n を含まない巡回に入った
        seen.add(x)
        if steps > CAP:
            raise RuntimeError("no descent or repeat within %d steps: q=%d n=%d" % (CAP, q, n))

for q in QS:
    mins = []
    for n in range(1, LIMIT):
        info = cycle_info(n, q)
        if info:
            mins.append((n, info[0], info[1]))
    # 出力: q<TAB>最小元のカンマ区切り<TAB>(最小元:長さ:奇数の個数) の一覧
    print("%d\t%s\t%s" % (q, ",".join(str(m[0]) for m in mins), " ".join("%d:%d:%d" % m for m in mins)))
