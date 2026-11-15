"""Independent exact checks for the complementary searches and block counting."""
from itertools import combinations_with_replacement
from math import comb, factorial, isqrt
from pathlib import Path
import json


def trial_divisors(number):
    values = []
    for divisor in range(1, isqrt(number) + 1):
        if number % divisor == 0:
            values.append(divisor)
            if divisor * divisor != number:
                values.append(number // divisor)
    return values


def check_two_channel(limit=1000):
    primes_checked = witnesses_checked = 0
    for prime in range(5, limit, 4):
        if any(prime % divisor == 0 for divisor in range(2, isqrt(prime) + 1)):
            continue
        primes_checked += 1
        budget = isqrt((prime + 1) // 4)
        full = set()
        for source in range(1, prime):
            for divisor in trial_divisors(prime + source):
                if divisor % 4 == 3 and (prime + divisor) % (4 * source) == 0:
                    auxiliary = (prime + divisor) // (4 * source)
                    assert (source - 1) * auxiliary <= (prime + 1) // 4
                    assert (4 * auxiliary + 1) % divisor == 0
                    full.add((source, auxiliary, divisor))
        first = {witness for witness in full if witness[0] <= budget + 1}
        second = set()
        for auxiliary in range(1, budget + 1):
            for divisor in trial_divisors(4 * auxiliary + 1):
                if divisor % 4 == 3 and (prime + divisor) % (4 * auxiliary) == 0:
                    source = (prime + divisor) // (4 * auxiliary)
                    second.add((source, auxiliary, divisor))
        assert full == first | second
        witnesses_checked += len(full)
    assert (30241 + 27) // (4 * 47) == 161
    assert 189 % 27 == 0
    return primes_checked, witnesses_checked


def check_sorting_bound():
    checked = 0
    for size in range(1, 7):
        for budget in range(10):
            sorted_vectors = sum(
                sum(vector) <= budget
                for vector in combinations_with_replacement(range(budget + 1), size)
            )
            assert sorted_vectors * factorial(size) >= comb(budget + size, size)
            checked += 1
    return checked


def main():
    primes, witnesses = check_two_channel()
    assert (primes, witnesses) == (80, 463)
    report = {
        "primes_below_1000_checked": primes,
        "complete_witnesses_checked": witnesses,
        "comparison": "Full witness set equals the union of both bounded channels",
        "exact_sorting_count_cases": check_sorting_bound(),
        "stronger_sieve_proof": "Analytic proof in sharper-large-sieve.tex",
    }
    path = Path(__file__).resolve().parents[2] / "source-search" / "two-channel-checks.json"
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
