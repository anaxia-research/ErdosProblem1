"""Reproduce the first-source census, using exact integer arithmetic."""
import argparse
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path
from source_search import smallest_factors, divisors, source_witness, denominators


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=1_000_000)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.limit < 5:
        parser.error("limit must be at least five")
    factors = smallest_factors(2 * args.limit)
    count, failures, worst, unresolved = 0, [], (0, 0, 0), []
    digest = sha256()
    for p in range(5, args.limit, 4):
        if factors[p] != p:
            continue
        count += 1
        for i in range(1, p):
            good = next((d for d in divisors(p + i, factors)
                         if source_witness(p, i, d)), None)
            if good is None:
                continue
            triple = denominators(p, i, good)
            record = f"{p},{i},{good},{triple[0]},{triple[1]},{triple[2]}\n"
            digest.update(record.encode("ascii"))
            if i > isqrt(p) // 2:
                failures.append({"p": p, "cutoff": isqrt(p) // 2,
                                 "first_source": i, "d": good, "denominators": triple})
            if i > worst[0]:
                worst = i, p, good
            break
        else:
            unresolved.append(p)
    result = {
        "limit_exclusive": args.limit, "primes_1_mod_4": count,
        "square_root_cutoff_failures": failures, "maximum_first_source": worst,
        "witness_sha256": digest.hexdigest(), "no_source_found_below_p": unresolved,
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
