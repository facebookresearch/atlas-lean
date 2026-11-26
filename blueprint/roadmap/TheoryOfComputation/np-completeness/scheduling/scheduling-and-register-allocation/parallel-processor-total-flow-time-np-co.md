# PARALLEL PROCESSOR TOTAL FLOW TIME is NP-complete

The [decision problem](parallel-processor-total-flow-time-dec.md) PARALLEL PROCESSOR TOTAL FLOW TIME belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Hardness comes from a special case: with one processor ($m = 1$) the total flow time is $\sum_t (C_t - r_t) = \sum_t C_t - \sum_t r_t$, so the bound $K$ on flow time is the bound $K + \sum_t r_t$ on total completion time. Single-machine scheduling with release times and a completion-time bound $J$ (strongly NP-hard, the cited result) maps to $K = J - \sum_t r_t$ when $J > \sum_t r_t$; otherwise it is a no-instance, since every task completes after its release time, and is mapped to a fixed no-instance.

## Sources

- P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem MINIMUM PARALLEL PROCESSOR TOTAL FLOW TIME (decision version).
- J. K. Lenstra, A. H. G. Rinnooy Kan and P. Brucker, "Complexity of machine scheduling problems", Annals of Discrete Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X (the case $m = 1$, $1|rⱼ|∑ Cⱼ$, is strongly NP-hard).
