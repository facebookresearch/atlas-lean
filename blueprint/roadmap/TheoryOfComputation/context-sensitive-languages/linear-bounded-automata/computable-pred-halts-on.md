# Halting of a machine running in computable space is computable

Let $M$ be a single-tape
machine with state set $Q$ over a finite alphabet $\Sigma$, fix any primitive recursive coding of
$\Sigma$, and let $s : \mathbb{N} \to \mathbb{N}$ be computable. If $M$ runs in space $s$, then the
set of input words over $\Sigma$ on which $M$ halts is computable.

The decision procedure runs $M$ for $(|Q| + 1)(|\Sigma| + 1)(|\Sigma| + 2)^{2 s(n)}$ steps on an
input of length $n$ and checks whether it has halted.
