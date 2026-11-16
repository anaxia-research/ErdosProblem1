# First denominators: formal and computational checks

Checks for the Erdős–Straus note on first denominators (Theorem 1 ratio criterion, Lemma 2,
Theorems 3 and 4, Corollaries 5 and 6, the m = 11 description, and the family p = 4acd − a − c).
Notation as in the paper: p ≡ 1 (mod 4) prime, 4x = p + m, R(x) = {u/v mod m : uv | x},
G = (Z/mZ)^×, H = stabiliser of R(x).

## lean/ (Lean 4 v4.34.1, Mathlib v4.34.1)

79 theorems, no `sorry`, no `axiom`, no `native_decide`. `Axioms.lean` prints the axioms of
every theorem; the output is in `lean/AXIOMS.txt` (each uses only propext, Classical.choice,
Quot.sound).

Kneser's theorem is not in Mathlib. It is vendored from Mantas Bakšys and Yaël Dillies'
formalisation (`Finset.mul_kneser`, github.com/YaelDillies/misc-yd at commit 338b7f4f, originally
in LeanCamCombi; Apache 2.0, licence in `lean/FirstDenominators/Vendor/`). The only edits remove
the module-system keywords. So Lemma 2 and Theorems 3 and 4 are proved with no hypotheses.

| File | What is proved |
|---|---|
| `Identities.lean` | Theorem 1, both explicit (y, z) identities (coprimality of u, v not needed) |
| `Criterion.lean` | Theorem 1 in full: x good ⇔ −1 ∈ R(x) or −p ∈ R(x) (`good_iff_isRatio`) |
| `RatioSet.lean` | R(x) = ∏ over prime factors q of x (with multiplicity) of {q⁻¹, 1, q} |
| `GroupCore.lean` | a subgroup omits the element ε of order 2 iff it has odd order (cyclic case included); c_H(q) = 1 forces q ∈ εH; the image of {q⁻¹,1,q} in G/H has 1 + c_H(q) elements; \|{q⁻¹,1,q}·H\| = \|H\|(1 + c_H(q)) |
| `Kneser.lean` | Kneser holds in every finite abelian group (`kneserHyp`); Lemma 2 (k sets); Theorem 3 and Theorem 4 (abstract forms, including the integer bound k* ≤ n/h − 1 − δ); Corollary 5 (a), (b) |
| `Main.lean` | Theorem 3 (any m), Theorem 4 (m = ℓ^j, ℓ an odd prime; also the first-kind variant), Corollary 5 (a), (b) with non-squares, the subgroup obstruction, the m = 3 description |
| `Reciprocity.lean` | (q/m) = (q/p) for q \| x; Corollary 5 (a), (b) with Ω_N as in the paper; Corollary 5 (c) |
| `M7.lean` | Corollary 6: the complete m = 7 description, as an iff for every prime p ≡ 1 (mod 4) |

Not formalised: the m = 11 description (checked in Julia only). Its "not good" direction would
follow the same pattern as `M7.lean`. The "good" direction needs a saturation argument over
infinitely many factor patterns, which was not done.

Theorem 4 in Lean is a little more general than the paper: it needs only ℓ odd, not m ≡ 3 (mod 4).

Build: `cd lean && lake exe cache get && lake build` (about 1 minute after the cache download).

## julia/ (Julia 1.11, no packages)

Run with `julia/run_all.sh`. Results are in `julia/results/`.

| Script | Check | Result |
|---|---|---|
| `check_thm1.jl` | Theorem 1 against a brute-force search over the divisors of (px)², all 101,715 pairs (p, m) with p < 2000; 7,006 explicit (y, z) checked in exact arithmetic | 0 mismatches |
| `check_thm34.jl` | Lemma 2 on all 221,394 pairs with p < 3000. Theorem 3 on the 216,765 failing pairs (equality in 242). Theorem 4 on the 58,617 failing prime-power pairs (equality in 164), plus its first-kind variant. Reciprocity (q/m) = (q/p): 504,695 checks. Corollary 5: (a) 232, (b) 210, (c) 206 instances | 0 violations |
| `check_m7_m11.jl` | Corollary 6 (m = 7) and the m = 11 description (17 exceptional multisets plus "all residues in {3,4,5,9}") against brute force, p < 200,000 (8,977 primes) | 0 mismatches |
| `exceptions.jl` | p = 4acd − a − c, using the form "p + a has a divisor ≡ −1 (mod 4a)". a = 1 is decided by a segmented sieve and a ≥ 2 by trial division. The search runs to a ≤ (1+√(1+4p))/4, which is exhaustive by the a ↔ c symmetry. A second brute force (4ac \| p + a + c) re-checks each exception. Threaded | see below |

Exceptions (primes p ≡ 1 mod 4 with no representation p = 4acd − a − c):

    409, 577, 5569, 9601, 23929, 83449, 102001, 329617, 712321,
    1134241, 1724209, 1726201, 5212561, 8813281

| Bound | Primes p ≡ 1 (mod 4) | Exceptions | Time |
|---|---|---|---|
| 10^9 | 25,423,491 | 14 | 8 s (4 threads) |
| 10^10 | 227,523,275 | 14 | 67 s (4 threads) |
| 10^11 | 2,059,020,280 | 14 | 21 min (3 threads) |

The list matches the paper's list (computed by `leastn.c`, a different algorithm) and extends
it from 10^10 to 10^11. Largest least a: 469, at p = 53,325,721.

## c/

`leastn.c` is the original program from the paper's computation. Rerun to 10^9
(`results_leastn_1e9.txt`): 25,423,491 primes and the same 14 failures.

## Discrepancies with the source report

None found. Every count and statement checked agrees with REPORT.md. Two statements hold more
generally than stated there:

- Theorem 1 does not need u and v coprime.
- Theorem 4 needs only m = ℓ^j with ℓ odd.
