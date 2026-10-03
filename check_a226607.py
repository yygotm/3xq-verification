# Cross-check of the cycle minima with OEIS A226607 (G. H. Morley).
# A226607 lists, for each k with gcd(k, 6) = 1 in increasing order, the smallest elements of the
# primitive cycles (all elements coprime to k) of T_k(x) = x/2 (x even), (3x + k)/2 (x odd).
# This script recomputes rows k = 1..97 by brute force (starting values below LIMIT), compares the
# flattened rows with the b-file, and checks that cycles.txt minus the trivial cycle {q, 2q}
# equals the primitive row for each prime q.
# Usage: python check_a226607.py b226607.txt [LIMIT]   (b-file: https://oeis.org/A226607/b226607.txt)
import sys
from math import gcd

def minima(k, limit):
    out = []
    for n in range(1, limit):
        x, seen = n, {n}
        while True:
            x = (3 * x + k) >> 1 if x & 1 else x >> 1
            if x < n:
                break
            if x == n:
                out.append(n)
                break
            if x in seen:
                break
            seen.add(x)
    return out

bfile = [int(l.split()[1]) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
limit = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
rows, flat = {}, []
for k in range(1, 98):
    if gcd(k, 6) != 1:
        continue
    rows[k] = [n for n in minima(k, limit) if gcd(n, k) == 1]
    flat += rows[k]
ok = flat == bfile[:len(flat)]
print("rows k=1..97: %d terms, equal to the first %d terms of the b-file: %s" % (len(flat), len(flat), ok))
for line in open('cycles.txt'):
    q, cms = line.split('\t')[:2]
    q = int(q)
    if q < 0:
        continue
    mine = [int(x) for x in cms.split(',') if int(x) != q]
    if mine != rows[q]:
        ok = False
        print("q=%d: cycles.txt %s != primitive row %s" % (q, mine, rows[q]))
print("OK" if ok else "MISMATCH")
sys.exit(0 if ok else 1)
