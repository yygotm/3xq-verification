# The 3x+q map for primes 5 <= q <= 97: every starting value below 2^48 reaches a known cycle

## Claim

For each prime `q` with `5 <= q <= 97` (23 primes), let

    T_q(x) = x/2         (x even)
    T_q(x) = (3x + q)/2  (x odd).

Every positive integer `n < 2^48` reaches, under iteration of `T_q`, one of the cycles whose
smallest elements are listed in `cycles.txt` (table below). Consequently, for these `q`:

- no trajectory starting below `2^48` diverges or ends in another cycle;
- the listed cycles are all the cycles of `T_q` that contain a positive integer below `2^48`
  (the smallest element of any other cycle would itself be a starting value below `2^48` that
  does not reach a listed cycle).

The cycle `{q, 2q}` is included for each `q`. The other entries are the primitive cycles (all
elements coprime to `q`).

| q | cycles | smallest elements |
|---|---|---|
| 5 | 6 | 1, 5, 19, 23, 187, 347 |
| 7 | 2 | 5, 7 |
| 11 | 3 | 1, 11, 13 |
| 13 | 10 | 1, 13, 131, 211, 227, 251, 259, 283, 287, 319 |
| 17 | 3 | 1, 17, 23 |
| 19 | 2 | 5, 19 |
| 23 | 4 | 5, 7, 23, 41 |
| 29 | 5 | 1, 11, 29, 3811, 7055 |
| 31 | 2 | 13, 31 |
| 37 | 4 | 19, 23, 29, 37 |
| 41 | 2 | 1, 41 |
| 43 | 2 | 1, 43 |
| 47 | 8 | 5, 25, 47, 65, 73, 85, 89, 101 |
| 53 | 2 | 53, 103 |
| 59 | 8 | 1, 59, 133, 149, 181, 185, 217, 221 |
| 61 | 3 | 1, 61, 235 |
| 67 | 2 | 17, 67 |
| 71 | 8 | 29, 31, 71, 2585, 2809, 3985, 4121, 4409 |
| 73 | 4 | 5, 19, 47, 73 |
| 79 | 5 | 1, 7, 79, 233, 265 |
| 83 | 4 | 65, 83, 109, 157 |
| 89 | 2 | 17, 89 |
| 97 | 3 | 1, 13, 97 |

Prior work: OEIS A226607 (G. H. Morley, 2013) lists the smallest elements of conjecturally all
primitive cycles of `3x+k`, found by following trajectories from starting values below `10^8`.
The present run checks every starting value below `2^48` (about `2.8 x 10^14`) for the 23 primes
above. We are not aware of an earlier exhaustive check for these `q` to this bound.

## Result

| quantity | value |
|---|---|
| range | `[1, 2^40)` and `[2^40, 2^48)` for each of the 23 primes |
| odd starting values accounted for, per prime | `2^39 = 549,755,813,888` below `2^40`; `140,187,732,541,440` in `[2^40, 2^48)` (= `2^47 - 2^39`) |
| chunks | 114 or 115 per prime below `2^40`; 15,167 per prime in `[2^40, 2^48)` (q = 5: 1,313 + 15,167); none missing or duplicated |
| failures (`FAIL` / `ALLFAIL` lines) | **0** |
| compute for `[2^40, 2^48)` | 99,768 s wall (about 27.7 h) on one laptop CPU (Intel Core i7-1355U, 12 hardware threads, Docker) |
| compute for `[1, 2^40)` | under 10 minutes for all 23 primes |

Each production log ends with an `ALLDONE ... OK` line in which the program itself re-reads all
`DONE` lines and checks that the per-chunk counts add up to the number of odd integers in the
range (`odd=... accounted=... OK`). Even `n` drop to `n/2 < n` in one step.

## Method (`verify_3xq.c`)

The program proves, by induction on `n`, that every `n` in `[LO, HI)` reaches a listed cycle,
assuming this for all `n < LO`. For each `n` (other than the listed minima) it finds a point `x`
on the trajectory of `n` such that

- (C) `x` is an element of a listed cycle, or
- (I) `x < n`, or
- (P) `x` has an ancestor `m = (2^k x + c)/3^a` with `1 <= m < n` (an inverse path of `T_q`
  determined by `x mod 3^L`; the trajectory of `m` passes through `x`).

A smallest counterexample would contradict each case. (C) is needed for `3x+q`: a number can
enter a cycle whose smallest element is larger than itself (`q = 5`: 3 -> 7 -> 13 -> 22 -> 11 -> 19);
it is checked for `n` up to the largest cycle element.

Odd `n` are grouped by `n mod 2^j` on a binary tree. The first `j` steps are common to a class,
and the members' values after `j` steps are `e + 3^a t`, so (I) and (P) can be decided for a
whole class from its two endpoints. Classes that are not closed this way are split until they
have at most `LEAFN` members, which are then traced one by one. At start-up the program follows
each listed minimum around its cycle and rejects a list entry that is not the minimum of a cycle.
A number whose trajectory meets none of (C), (I), (P) within 100,000 steps, or exceeds `2^125`,
is reported as `FAIL` (so an unlisted cycle or a divergent trajectory cannot pass silently).

The program is a generalisation of `verify2.c` from the `3x-1` verification
(Shimizu, *3x-1-verification* v0.4.0, https://doi.org/10.5281/zenodo.23047609).

## Validation (`run.sh`, output in `logs/tests_run.out`)

- **Self-check mode** (mode 2): every class closed by (I)/(P) and every traced number is
  re-checked by naive forward iteration, including each (P) certificate (`m` is a positive
  integer, `m < n`, and `T_q^k(m) = x`). All 23 primes on `[1, 2^22)` and
  `[2^40, 2^40 + 2^20)`: `selfcheck_bad=0`.
- **Exact mode** (mode 1, without (P)) on `[1, 2^20)` and the production path (mode 0) on
  `[2^40, 2^40 + 2^20)`: all OK.
- **Regression against `verify2.c`** (a copy that differs from the published file only in one
  comment line) for `q = -1` (the `3x-1` map): identical statistics on 6 of
  7 ranges. On the 7th all counts agree and both report `maxsteps=260`; only the witness `n` of
  that tie differs, and it varies between repeated multi-threaded runs of the same binary.
- **Failure detection**: `q = 5` with the cycle of 19 removed from the list reports `FAIL`
  (exit 2). A sampled benchmark run (`BENCH_STRIDE`) exits 4, never 0.
- **Checkpointing**: a resumed run accepts only `DONE` lines written by the same source and
  build (`src=` hash and build constants in each line).
- **Cycle list**: `enum_cycles.py` finds the minima by brute force from starting values below
  200,000. `check_a226607.py` recomputes the primitive-cycle rows for all `k <= 97` with
  `gcd(k, 6) = 1`; the 89 values equal the first 89 terms of the OEIS A226607 b-file, and
  `cycles.txt` minus `{q, 2q}` equals the row of each `q` (`logs/check_a226607.out`).
- All production logs carry `src=a5fc0a7c6d12` (first 12 hex digits of the MD5 of
  `verify_3xq.c`).

## Limitations

- The result rests on a single implementation. The self-check, exact-mode and regression tests
  above cover small ranges and one range near `2^40`; the production ranges were run in mode 0
  only.
- This is a finite verification, not a proof.

## Reproduce

Requires gcc with OpenMP and Python 3 (tested with gcc 12.2.0 and Python 3.11 in the
`node:24-bookworm` Docker image). The scripts expect this directory at `/w`; `run.sh` also
expects `verify2.c` from the `3x-1` record above at `/m/verify2.c` (only for the `q = -1`
regression).

```sh
bash run.sh                    # builds verify_3xq (src= hash from md5sum) and runs the tests
cp verify_3xq prod/verify_3xq_prod
bash prod/run_all_2p40.sh      # [1, 2^40) for all primes
bash prod/run_q5_scale.sh      # q = 5, [2^40, 2^48) in two ranges
bash prod/run_all_2p48.sh      # [2^40, 2^48) for the other 22 primes
python check_a226607.py b226607.txt
```

Usage of the program: `verify_3xq <q> <cycle minima> <LO> <HI> <mode> [F L LEAFN [chunk logfile]]`.
With a chunk size and a log file it checkpoints: rerunning the same command skips finished
chunks. `prod/*_summary.txt` collect the final lines; wall-clock times of day were removed from
them. `SHA256SUMS` lists the hashes of the files in this archive.
