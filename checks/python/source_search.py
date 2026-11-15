"""Exact checks and finite searches for the bounded Type I source paper.

All rational identities are checked by integer arithmetic.  A finite
verification supplies no conclusion about primes above the printed limit.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
from math import isqrt
import json
from pathlib import Path


def smallest_factors(limit):
    factors = list(range(limit + 1))
    for prime in range(2, isqrt(limit) + 1):
        if factors[prime] == prime:
            for multiple in range(prime * prime, limit + 1, prime):
                if factors[multiple] == multiple:
                    factors[multiple] = prime
    return factors


def divisors(number, factors):
    values = [1]
    while number > 1:
        prime = factors[number]
        power = 1
        extension = []
        while number % prime == 0:
            number //= prime
            power *= prime
            extension.extend(value * power for value in values)
        values.extend(extension)
    return sorted(values)


def source_witness(prime, source, divisor):
    return (prime + source) % divisor == 0 and divisor % 4 == 3 and (
        prime + divisor
    ) % (4 * source) == 0


def denominators(prime, source, divisor):
    assert source_witness(prime, source, divisor)
    step = (prime + divisor) // (4 * source)
    cofactor = (prime + source) // divisor
    result = source * step, source * step * cofactor, prime * step * cofactor
    x, y, z = result
    assert min(result) > 0
    assert 4 * x * y * z == prime * (x * y + x * z + y * z)
    assert x % prime and y % prime and z % prime == 0
    return result


def complete_three_term_search(number):
    """All ordered triples are represented by the first denominator and a factor pair."""
    for x in range(number // 4 + 1, 3 * number // 4 + 1):
        numerator = 4 * x - number
        product = number * x
        for left in range(1, product + 1):
            if product * product % left:
                continue
            right = product * product // left
            if (product + left) % numerator or (product + right) % numerator:
                continue
            y, z = (product + left) // numerator, (product + right) // numerator
            if x <= y <= z:
                assert 4 * x * y * z == number * (x * y + x * z + y * z)
                return x, y, z
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=200_000)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.limit < 100:
        parser.error("limit must be at least 100")
    factors = smallest_factors(max(args.limit + isqrt(args.limit) + 5, 401))
    prime_values = [p for p in range(2, max(args.limit, 301)) if factors[p] == p]
    primes = [p for p in prime_values if p < args.limit and p % 4 == 1]
    checked_pairs = certificates_a = certificates_b = 0
    failures = []
    census_hash = sha256()
    maximum_source = (0, 0, 0)
    survivor_counts = dict.fromkeys((1, 2, 3, 5, 10, 32), 0)
    for p in primes:
        depth = isqrt(p) // 2
        first = None
        for i in range(1, depth + 1):
            checked_pairs += 1
            ds = divisors(p + i, factors)
            witnesses = [d for d in ds if source_witness(p, i, d)]
            if witnesses and first is None:
                first = i, witnesses[0]
            for q in ds:
                if q <= 1 or factors[q] != q:
                    continue
                if (q + p) % (4 * i) == 0:
                    certificates_a += 1
                    denominators(p, i, q)
            if i % 2 == 0:
                # The cofactor rule is valid for every divisor q, including composites.
                for q in ds:
                    old_rule = (q * p + p + i) % (4 * i) == 0
                    new_rule = (q + 1 + i) % (4 * i) == 0
                    assert old_rule == new_rule
                    if new_rule:
                        certificates_b += 1
                        denominators(p, i, (p + i) // q)
            if witnesses:
                denominators(p, i, witnesses[0])
        if first is None:
            failures.append(p)
        else:
            i, d = first
            x, y, z = denominators(p, i, d)
            census_hash.update(f"{p},{i},{d},{x},{y},{z}\n".encode("ascii"))
            if i > maximum_source[0]:
                maximum_source = i, p, d
        for cutoff in survivor_counts:
            if depth >= cutoff and (first is None or first[0] > cutoff):
                survivor_counts[cutoff] += 1

    omega = {}
    beyond_cutoff = []
    for p in failures:
        for i in range(isqrt(p) // 2 + 1, p):
            ds = divisors(p + i, factors) if p + i < len(factors) else [
                d for d in range(1, p + i + 1) if (p + i) % d == 0
            ]
            good = [d for d in ds if source_witness(p, i, d)]
            if good:
                beyond_cutoff.append({
                    "p": p, "cutoff": isqrt(p) // 2, "first_source": i,
                    "d": good[0], "denominators": denominators(p, i, good[0])
                })
                break
    if args.limit > 30241:
        assert beyond_cutoff[0] == {
            "p": 30241, "cutoff": 86, "first_source": 161,
            "d": 27, "denominators": (7567, 8520442, 1600414202)
        }
    for f in prime_values:
        if f == 2:
            omega[f] = 0
            continue
        residues = []
        for m in divisors(f + 1, factors):
            if m % 4 == 3:
                i = (f + 1) // m
                assert i % 2 == 0 and 2 <= i <= (f + 1) // 3 < f
                residues.append((-i) % f)
        assert len(set(residues)) == len(residues)
        assert 0 not in residues and 1 not in residues
        omega[f] = len(residues)
    assert [omega[p] for p in (3, 5, 7, 11, 29)] == [0, 1, 0, 1, 2]

    phi = list(range(401))
    for p in range(2, len(phi)):
        if phi[p] == p:
            for n in range(p, len(phi), p):
                phi[n] -= phi[n] // p
    kappas = {
        m: str(sum((Fraction(1, phi[4 * i]) for i in range(1, m + 1)), Fraction()))
        for m in (1, 2, 3, 5, 10, 32, 100)
    }
    assert kappas[1] == "1/2" and kappas[2] == "3/4"

    qmax = 300
    weights = [Fraction() for _ in range(qmax + 1)]
    weights[1] = Fraction(1)
    for q in range(2, qmax + 1):
        p = factors[q]
        rest = q // p
        if rest % p and omega[p]:
            weights[q] = weights[rest] * Fraction(omega[p], p - omega[p])
    large_sieve_values = {q: str(sum(weights[:q + 1], Fraction())) for q in (10, 30, 100, 300)}

    # Both directions of the factorization parameterization on small inputs.
    for n in range(2, 301):
        assert complete_three_term_search(n) is not None
    for n in range(2, 40):
        for x in range(n // 4 + 1, 3 * n // 4 + 1):
            a, b = 4 * x - n, n * x
            for y in range(x, 100):
                if a * y <= b:
                    continue
                top, bottom = b * y, a * y - b
                if top % bottom == 0 and top // bottom >= y:
                    z = top // bottom
                    left, right = a * y - b, a * z - b
                    assert left * right == b * b and 1 <= left <= b

    result = {
        "scope": "Finite exact checks of source certificates and search reductions",
        "prime_limit_exclusive": args.limit,
        "primes_1_mod_4": len(primes),
        "source_pairs_checked": checked_pairs,
        "prime_divisor_rule_hits": certificates_a,
        "cofactor_rule_hits_including_composites": certificates_b,
        "square_root_search_failures": failures,
        "first_sources_beyond_cutoff": beyond_cutoff,
        "maximum_first_source_among_cutoff_successes": {"i": maximum_source[0], "p": maximum_source[1], "d": maximum_source[2]},
        "first_witness_census_sha256": census_hash.hexdigest(),
        "bounded_search_survivors_when_depth_allows": survivor_counts,
        "kappa_exact": kappas,
        "large_sieve_L_exact": large_sieve_values,
        "general_three_term_search_checked_through": 300,
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
