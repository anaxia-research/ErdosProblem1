# Corollary 6 (m = 7) and the m = 11 description: x = (p + m)/4, p = 1 mod 4 prime, 5 <= p < P.
# "good" is decided by brute force on the divisors of (px)^2 (independent of Theorem 1)
# and also by the ratio criterion.
# Usage: julia check_m7_m11.jl [P=20000]
include("common.jl")

function bad7(fx)
    cnt(rs) = sum(v for (q, v) in fx if q % 7 in rs; init = 0)
    g = cnt((6,)); a3 = cnt((3,)); a5 = cnt((5,)); b = cnt((2, 4))
    return g == 0 && ((a3 + a5 == 0) || (b == 0 && a5 == 0 && a3 in (1, 2)))
end

const M11 = Set([sort(v) for v in [[2],[6],[7],[2,3],[3,6],[5,7],[2,6],[2,7],[6,6],[7,7],[2,3,6],[5,7,7],
                                   [2,6,6],[6,6,6],[7,7,7],[2,6,6,6],[7,7,7,7]]])
function bad11(fx)
    Mset = sort(vcat([fill(q % 11, v) for (q, v) in fx if q % 11 != 1]...))
    return all(r in (3, 4, 5, 9) for r in Mset) || Mset in M11
end

function main(P)
    out = ""
    for (m, bad, name) in ((7, bad7, "Corollary 6 (m = 7)"), (11, bad11, "m = 11 description"))
        n = 0; nbad = 0; mism = 0; mismR = 0; ex = String[]
        for p in primes_upto(P - 1)
            (p % 4 == 1 && p >= 5) || continue
            x = (p + m) ÷ 4
            fx = factor_trial(x, primes_upto(isqrt(x) + 1))
            g = good_direct(p, x, mergef(fx, [(p, 1)]))
            S, _ = ratio_set(fx, m)
            gR = S[m - 1 + 1] || S[mod(-p, m) + 1]
            n += 1; nbad += !g
            g == gR || (mismR += 1)
            if g == bad(fx)
                mism += 1; push!(ex, "p=$p x=$x f=$fx good=$g")
            end
        end
        out *= "$name, primes 5 <= p < $P, p = 1 mod 4: $n primes, $nbad with x = (p+$m)/4 not good\n" *
               "  mismatches with the stated description: $mism   brute force vs ratio criterion: $mismR\n"
        for e in ex[1:min(10, length(ex))]; out *= "  $e\n"; end
    end
    return out
end

P = length(ARGS) >= 1 ? parse(Int, ARGS[1]) : 20000
t = @elapsed out = main(P)
out *= "time: $(round(t, digits=1)) s\n"
print(out)
write(joinpath(@__DIR__, "results", "m7_m11_$(P).txt"), out)
