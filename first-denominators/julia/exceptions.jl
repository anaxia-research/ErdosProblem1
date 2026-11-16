# Section 3: primes p = 1 (mod 4) with no representation p = 4acd - a - c (a, c, d >= 1).
#
# Independent of leastn.c.  Form used: p = 4acd - a - c  <=>  p + a = c (4ad - 1)
#   <=>  p + a has a divisor t = -1 (mod 4a)   (then d = (t+1)/(4a), c = (p+a)/t).
# By the symmetry a <-> c a representation has min(a, c) <= amax(p) = floor((1 + sqrt(1+4p))/4),
# because p + a >= c(4a - 1) >= a(4a - 1).  So "no a <= amax(p) works" proves p is an exception.
#
# a = 1 is decided for every prime by a segmented sieve: p + 1 = 2M has a divisor = 3 (mod 4)
# iff M has a prime factor = 3 (mod 4).  The remaining primes try a = 2, 3, ... by trial-division
# factorisation of p + a and enumeration of divisors.
#
# Usage: julia -t 4 exceptions.jl N [chunk_k]
using Base.Threads

include("common.jl")

isqrt_floor(n::Int) = (r = isqrt(n); r)
amax(p::Int) = (1 + isqrt_floor(1 + 4p)) ÷ 4

"Does N have a divisor t with t = r (mod mod)?  f = factorisation of N."
function has_divisor_class(f::Vector{Tuple{Int,Int}}, r::Int, md::Int)
    # residues of divisors mod md, built as a set (md small) or by enumeration
    res = falses(md); res[1 % md + 1] = true
    for (q, e) in f
        qm = q % md
        cur = findall(res) .- 1
        for s in cur
            t = s
            for _ in 1:e
                t = t * qm % md
                res[t + 1] = true
            end
        end
        res[r + 1] && return true
    end
    return res[r + 1]
end

"Least a <= amax(p) such that p + a has a divisor = -1 mod 4a, starting at a0; 0 if none."
function least_a(p::Int, a0::Int, ps::Vector{Int})
    A = amax(p)
    for a in a0:A
        md = 4a
        f = factor_trial(p + a, ps)
        has_divisor_class(f, md - 1, md) && return a
    end
    return 0
end

struct ChunkResult
    nprimes::Int
    slow::Int
    fails::Vector{Int}
    maxa::Int
    maxa_p::Int
    hist::Vector{Int}   # hist[a] for a <= 64, hist[65] = a > 64
end

function process_chunk(k0::Int, k1::Int, N::Int, ps::Vector{Int})
    # p = 4k + 1, k in [k0, k1), p <= N
    K = k1 - k0
    isp = trues(K)
    rem = Vector{Int}(undef, K)
    f3 = falses(K)
    @inbounds for i in 1:K
        rem[i] = 2(k0 + i - 1) + 1          # M = (p + 1)/2
    end
    k0 == 0 && (isp[1] = false)               # p = 1
    pmax = 4(k1 - 1) + 1
    @inbounds for q in ps
        q == 2 && continue
        if q * q <= pmax
            # primality of p = 4k+1: p = q^2 + 4qj
            s = (q * q - 1) ÷ 4
            st = s >= k0 ? s : k0 + mod(s - k0, q)
            for k in st:q:(k1-1)
                isp[k - k0 + 1] = false
            end
        end
        # factor M = 2k + 1 (M <= 2k1): q | M  <=>  k = (q-1)/2 mod q
        if q * q <= 2k1 + 1
            s = (q - 1) ÷ 2
            st = k0 + mod(s - k0, q)
            is3 = (q & 3) == 3
            for k in st:q:(k1-1)
                i = k - k0 + 1
                r = rem[i] ÷ q
                while r % q == 0
                    r ÷= q
                end
                rem[i] = r
                is3 && (f3[i] = true)
            end
        elseif q * q > pmax
            break
        end
    end
    nprimes = 0; slow = 0; fails = Int[]; maxa = 0; maxa_p = 0; hist = zeros(Int, 65)
    @inbounds for i in 1:K
        isp[i] || continue
        p = 4(k0 + i - 1) + 1
        p > N && break
        nprimes += 1
        if f3[i] || (rem[i] > 1 && (rem[i] & 3) == 3)
            a = 1
        else
            slow += 1
            a = least_a(p, 2, ps)
        end
        if a == 0
            push!(fails, p)
        else
            hist[min(a, 65)] += 1
            if a > maxa
                maxa = a; maxa_p = p
            end
        end
    end
    return ChunkResult(nprimes, slow, fails, maxa, maxa_p, hist)
end

function run(N::Int; chunk::Int = 1 << 20)
    ps = primes_upto(isqrt(N + amax(N)) + 1000)
    kmax = (N - 1) ÷ 4 + 1                    # k in [0, kmax)
    starts = collect(0:chunk:kmax-1)
    results = Vector{ChunkResult}(undef, length(starts))
    done = Atomic{Int}(0)
    t0 = time()
    @threads :dynamic for j in eachindex(starts)
        k0 = starts[j]; k1 = min(k0 + chunk, kmax)
        results[j] = process_chunk(k0, k1, N, ps)
        d = atomic_add!(done, 1) + 1
        if d % max(1, length(starts) ÷ 20) == 0
            println(stderr, "  $(d)/$(length(starts)) chunks, $(round(time() - t0, digits=0)) s"); flush(stderr)
        end
    end
    np = sum(r.nprimes for r in results); sl = sum(r.slow for r in results)
    fails = sort(vcat([r.fails for r in results]...))
    best = argmax([r.maxa for r in results])
    hist = sum(r.hist for r in results)
    return np, sl, fails, results[best].maxa, results[best].maxa_p, hist, time() - t0
end

"Second, brute-force check of the exceptions: no a <= c with 4ac | p + a + c."
function brute_no_rep(p::Int)
    for a in 1:amax(p)
        cmax = (p + a) ÷ (4a - 1)
        for c in a:cmax
            (p + a + c) % (4a * c) == 0 && return false
        end
    end
    return true
end

if abspath(PROGRAM_FILE) == @__FILE__
    N = parse(Int, ARGS[1])
    chunk = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 1 << 20
    np, sl, fails, maxa, maxa_p, hist, t = run(N; chunk = chunk)
    io = IOBuffer()
    println(io, "Section 3 check: primes p = 1 (mod 4), 5 <= p <= $N, representation p = 4acd - a - c")
    println(io, "method: least a with a divisor of p + a that is -1 mod 4a (a = 1 by sieve, others by trial division);")
    println(io, "        exhaustive up to amax(p) = floor((1+sqrt(1+4p))/4), which suffices by the a <-> c symmetry")
    println(io, "threads: $(nthreads())   time: $(round(t, digits=1)) s")
    println(io, "primes p = 1 mod 4 checked: $np")
    println(io, "primes not settled by a = 1 (sent to trial division): $sl")
    println(io, "primes with no representation: $(length(fails))")
    println(io, "list: ", join(fails, ", "))
    bf = [brute_no_rep(p) for p in fails]
    println(io, "independent brute force (all a <= c with 4ac | p+a+c) confirms no representation: ", all(bf), " ($(count(bf))/$(length(fails)))")
    println(io, "largest least a: a = $maxa at p = $maxa_p")
    println(io, "distribution of least a (a: count): ", join(["$a: $(hist[a])" for a in 1:64 if hist[a] > 0], ", "),
            hist[65] > 0 ? ", >64: $(hist[65])" : "")
    out = String(take!(io))
    print(out)
    write(joinpath(@__DIR__, "results", "exceptions_$(N).txt"), out)
end
