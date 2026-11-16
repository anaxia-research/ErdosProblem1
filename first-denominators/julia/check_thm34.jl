# Lemma 2, Theorem 3, Theorem 4 (with its first-kind variant) and Corollary 5 (a), (b), (c)
# on all pairs (p, m), p = 1 mod 4 prime, 5 <= p < P, m = 4x - p, p/4 < x < p.
# Usage: julia check_thm34.jl [P=3000]
include("common.jl")

"Jacobi symbol (a/n), n odd positive."
function jacobi(a::Int, n::Int)
    a = mod(a, n); r = 1
    while a != 0
        while iseven(a)
            a ÷= 2
            (n % 8 == 3 || n % 8 == 5) && (r = -r)
        end
        a, n = n, a
        (a % 4 == 3 && n % 4 == 3) && (r = -r)
        a = mod(a, n)
    end
    return n == 1 ? r : 0
end

function main(P)
    spf = spf_table(4P)
    c = Dict{String,Int}()
    inc(k, v = 1) = (c[k] = get(c, k, 0) + v)
    viol = String[]
    for p in primes_upto(P - 1)
        (p % 4 == 1 && p >= 5) || continue
        for m in 3:4:(3p - 1)
            x = (p + m) ÷ 4
            x < p || break
            fx = factor_spf(x, spf)
            S, elems = ratio_set(fx, m)
            first = S[m - 1 + 1]                  # -1 in R
            good = first || S[mod(-p, m) + 1]
            inc("pairs")
            # stabiliser H of R (H is inside R since 1 is in R)
            H = [h for h in elems if all(S[(h * s) % m + 1] for s in elems)]
            Hs = falses(m); for h in H; Hs[h + 1] = true; end
            phi = totient(m, spf); h = length(H); idx = phi ÷ h
            phi % h == 0 || push!(viol, "H not a subgroup? p=$p m=$m")
            cfun(q) = Hs[q % m + 1] ? 0 : (Hs[(q * q) % m + 1] ? 1 : 2)
            sumc = sum(v * cfun(q) for (q, v) in fx; init = 0)
            kstar = sum(v for (q, v) in fx if !Hs[q % m + 1]; init = 0)
            # Lemma 2 (Kneser for k sets) on every pair: |R/H| >= 1 + sum c_H
            length(elems) % h == 0 || push!(viol, "R not a union of H-cosets p=$p m=$m")
            if length(elems) ÷ h < 1 + sumc
                push!(viol, "LEMMA2 p=$p m=$m")
            end
            inc("lemma2 checked")
            pp = prime_power(m, spf)
            n = phi ÷ 2
            delta = Hs[p % m + 1] ? 0 : 1
            if !good
                inc("failing pairs")
                Hs[m - 1 + 1] && push!(viol, "THM3 -1 in H p=$p m=$m")
                if sumc > idx - 2 - delta
                    push!(viol, "THM3 bound p=$p m=$m x=$x")
                elseif sumc == idx - 2 - delta
                    inc("thm3 equality")
                end
                if pp !== nothing
                    inc("thm4 failing prime-power pairs")
                    (isodd(h) && n % h == 0) || push!(viol, "THM4 h p=$p m=$m")
                    any(Hs[((m - 1) * q) % m + 1] for (q, _) in fx) && push!(viol, "THM4 item1 p=$p m=$m")
                    kstar <= n ÷ h - 1 - delta || push!(viol, "THM4 item2 p=$p m=$m")
                    kstar == n ÷ h - 1 - delta && inc("thm4 equality")
                end
            end
            if !first
                inc("first-kind failing pairs")
                sumc <= idx - 2 || push!(viol, "THM3 first-kind p=$p m=$m")
                if pp !== nothing
                    (isodd(h) && n % h == 0) || push!(viol, "THM4fk h p=$p m=$m")
                    any(Hs[((m - 1) * q) % m + 1] for (q, _) in fx) && push!(viol, "THM4fk item1 p=$p m=$m")
                    kstar <= n ÷ h - 1 || push!(viol, "THM4fk item2 p=$p m=$m")
                end
            end
            # reciprocity used in Cor 5: (q/m) = (q/p) for every prime q | x
            for (q, _) in fx
                inc("reciprocity checks")
                jacobi(q, m) == legendre(q, p) || push!(viol, "RECIPROCITY p=$p m=$m q=$q")
            end
            if pp !== nothing
                ON = sum(v for (q, v) in fx if legendre(q, p) == -1; init = 0)
                if ON >= n
                    inc("cor5a instances"); first || push!(viol, "COR5a p=$p m=$m")
                end
                if ON >= n - 1 && p % m != 1
                    inc("cor5b instances"); good || push!(viol, "COR5b p=$p m=$m")
                end
                ell, j = pp
                if j == 1 && isprime_small(n) && ON >= 1
                    k = sum(v for (q, v) in fx if q % m != 1; init = 0)
                    if k >= n
                        inc("cor5c instances (>= n)"); good || push!(viol, "COR5c p=$p m=$m")
                    elseif k >= n - 1 && p % m != 1
                        inc("cor5c instances (n-1, p != 1 mod m)"); good || push!(viol, "COR5c' p=$p m=$m")
                    end
                end
            end
        end
    end
    out = "Lemma 2 / Theorems 3, 4 / Corollary 5, primes 5 <= p < $P, p = 1 mod 4, all m = 4x - p\n"
    for k in sort(collect(keys(c))); out *= "  $k: $(c[k])\n"; end
    out *= "violations: $(length(viol))\n" * join(first_n(viol, 20), "\n") * (isempty(viol) ? "" : "\n")
    return out
end
first_n(v, k) = v[1:min(k, length(v))]
isprime_small(n) = n >= 2 && all(n % d != 0 for d in 2:isqrt(n))

P = length(ARGS) >= 1 ? parse(Int, ARGS[1]) : 3000
t = @elapsed out = main(P)
out *= "time: $(round(t, digits=1)) s\n"
print(out)
write(joinpath(@__DIR__, "results", "thm34_cor5.txt"), out)
