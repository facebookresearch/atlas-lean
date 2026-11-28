# Reversible Resolution is not simulated by Nullstellensatz over any field

There are $n$-variate CNF formulas $F_n$ with constant-width, polynomial-size Reversible Resolution refutations such that every $\mathbb F$-Nullstellensatz refutation of $F_n$, over any field $\mathbb F$, has degree $n^{\Omega(1)}$; lifting strengthens this to an exponential size lower bound. Hence RevRes is not $p$-simulated by $\mathbb F$-NS, strengthening the classical fact that Resolution is not, witnessed by sink-of-dag and pebbling formulas.

## Proof sketch

Take a sparse constant-width variant of $\mathrm{SoPL}_n$ (replacing long pointer clauses by a bounded-degree gadget). Its RevRes refutation walks the potential line and consumes clauses step by step, first in width $O(\log n)$ and then in constant width for the sparse version. The degree lower bound is the approximate and exact Nullstellensatz lemma for $\mathrm{SoPL}_n$, which survives the sparsification.

## Depends on

- [Reversible Resolution: a MaxSAT-style fragment of Resolution with consumed premises](reversible-resolution.md)

## Proof depends on

- [Approximate Nullstellensatz lower bound for the sink-of-potential-line formulas via approximate degree of OR](approximate-nullstellensatz-sink-of-potential-line.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
