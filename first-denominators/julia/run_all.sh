#!/usr/bin/env bash
# Runs every Julia check; results go to julia/results/*.txt
set -euo pipefail
cd "$(dirname "$0")"
julia check_thm1.jl 2000
julia check_thm34.jl 3000
julia check_m7_m11.jl 20000
julia check_m7_m11.jl 200000
julia -t 4 exceptions.jl 1000000000
julia -t 4 exceptions.jl 10000000000
# julia -t 4 exceptions.jl 100000000000   # about 21 min wall on 3 threads
