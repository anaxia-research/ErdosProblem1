# Shared helpers for the first-denominator checks (no packages needed).

"Primes up to n by the sieve of Eratosthenes."
function primes_upto(n::Int)
    s = trues(n)
    n >= 1 && (s[1] = false)
    i = 2
    while i * i <= n
        if s[i]
            for j in i*i:i:n
                s[j] = false
            end
        end
        i += 1
    end
    return [i for i in 2:n if s[i]]
end

"Smallest-prime-factor table on 1:n."
function spf_table(n::Int)
    spf = collect(0:n)
    i = 2
    while i * i <= n
        if spf[i+1] == i
            for j in i*i:i:n
                spf[j+1] == j && (spf[j+1] = i)
            end
        end
        i += 1
    end
    return spf
end

"Factorisation of x as a vector of (prime, exponent), using an spf table."
function factor_spf(x::Int, spf::Vector{Int})
    f = Tuple{Int,Int}[]
    while x > 1
        q = spf[x+1]; e = 0
        while x % q == 0
            x ÷= q; e += 1
        end
        push!(f, (q, e))
    end
    return f
end

"Factorisation by trial division with a list of primes covering sqrt(x)."
function factor_trial(x::Int, ps::Vector{Int})
    f = Tuple{Int,Int}[]
    for q in ps
        q * q > x && break
        if x % q == 0
            e = 0
            while x % q == 0
                x ÷= q; e += 1
            end
            push!(f, (q, e))
        end
    end
    x > 1 && push!(f, (x, 1))
    return f
end

"All divisors from a factorisation (Int128 to be safe for squares)."
function divisors_of(f::Vector{Tuple{Int,Int}})
    ds = Int128[1]
    for (q, e) in f
        cur = copy(ds)
        pw = Int128(1)
        for _ in 1:e
            pw *= q
            append!(cur, ds .* pw)
        end
        ds = cur
    end
    return ds
end

squaref(f) = [(q, 2e) for (q, e) in f]

function mergef(f::Vector{Tuple{Int,Int}}, g::Vector{Tuple{Int,Int}})
    d = Dict{Int,Int}()
    for (q, e) in f; d[q] = get(d, q, 0) + e; end
    for (q, e) in g; d[q] = get(d, q, 0) + e; end
    return sort([(q, e) for (q, e) in d])
end

"""
Direct test, independent of the ratio form: x is good for p iff (px)^2 has a
divisor d with d ≡ -px (mod m), m = 4x - p.  (m/(px) = 1/y + 1/z  <=>
(my - px)(mz - px) = (px)^2.)
"""
function good_direct(p::Int, x::Int, fpx::Vector{Tuple{Int,Int}})
    m = 4x - p
    B = Int128(p) * x
    for d in divisors_of(squaref(fpx))
        (d + B) % m == 0 && return true
    end
    return false
end

"R(x) = { prod q^{e_q} mod m : |e_q| <= v_q } as a BitVector indexed by residue+1."
function ratio_set(f::Vector{Tuple{Int,Int}}, m::Int)
    S = falses(m); S[1 % m + 1] = true
    elems = [1 % m]
    for (q, v) in f
        qi = invmod(q, m)
        new = Int[]
        for s in elems
            t = s; u = s
            for _ in 0:v
                push!(new, t); push!(new, u)
                t = t * q % m; u = u * qi % m
            end
        end
        S = falses(m)
        for r in new; S[r+1] = true; end
        elems = [r - 1 for r in findall(S)]
    end
    return S, elems
end

legendre(a::Int, p::Int) = powermod(a, (p - 1) ÷ 2, p) == 1 ? 1 : -1

"(prime, exponent) if m is a prime power, else nothing."
function prime_power(m::Int, spf)
    f = factor_spf(m, spf)
    length(f) == 1 ? f[1] : nothing
end

totient(m::Int, spf) = prod((q - 1) * q^(e - 1) for (q, e) in factor_spf(m, spf); init = 1)
