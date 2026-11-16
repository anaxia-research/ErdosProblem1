# Theorem 1: x good  <=>  -1 in R(x) or -p in R(x); and the two explicit (y, z) formulas.
# Usage: julia check_thm1.jl [P=2000]
include("common.jl")

function main(P)
    spf = spf_table(4P)
    pairs = 0; mism = 0; ngood = 0; sols = 0; bad_sol = 0
    for p in primes_upto(P - 1)
        (p % 4 == 1 && p >= 5) || continue
        for m in 3:4:(3p - 1)
            x = (p + m) ÷ 4
            x < p || break
            fx = factor_spf(x, spf)
            g1 = good_direct(p, x, mergef(fx, [(p, 1)]))
            S, _ = ratio_set(fx, m)
            g2 = S[m - 1 + 1] || S[mod(-p, m) + 1]
            pairs += 1; ngood += g1
            if g1 != g2
                mism += 1; println("MISMATCH p=$p m=$m x=$x")
            end
            # explicit formulas, for every coprime pair (u, v) with uv | x
            for u in divisors_of(fx), v in divisors_of(fx)
                u = Int(u); v = Int(v)
                (gcd(u, v) == 1 && x % (u * v) == 0) || continue
                if (u + v) % m == 0
                    y = big(p) * (x ÷ v) * ((u + v) ÷ m); z = big(p) * (x ÷ u) * ((u + v) ÷ m)
                    sols += 1
                    (y > 0 && z > 0 && 4 // big(p) == 1 // big(x) + 1 // y + 1 // z) || (bad_sol += 1)
                end
                if (u + p * v) % m == 0
                    y = big(p) * (x ÷ u) * ((u + p * v) ÷ m); z = big(x ÷ v) * ((u + p * v) ÷ m)
                    sols += 1
                    (y > 0 && z > 0 && 4 // big(p) == 1 // big(x) + 1 // y + 1 // z) || (bad_sol += 1)
                end
            end
        end
    end
    return "Theorem 1, primes 5 <= p < $P, p = 1 mod 4, all m = 4x - p with p/4 < x < p\n" *
           "pairs (p,m) checked: $pairs   good (brute force on divisors of (px)^2): $ngood\n" *
           "mismatches between brute force and ratio criterion: $mism\n" *
           "explicit solutions from the two formulas checked in exact arithmetic: $sols   failures: $bad_sol\n"
end

P = length(ARGS) >= 1 ? parse(Int, ARGS[1]) : 2000
t = @elapsed out = main(P)
out *= "time: $(round(t, digits=1)) s\n"
print(out)
write(joinpath(@__DIR__, "results", "thm1.txt"), out)
