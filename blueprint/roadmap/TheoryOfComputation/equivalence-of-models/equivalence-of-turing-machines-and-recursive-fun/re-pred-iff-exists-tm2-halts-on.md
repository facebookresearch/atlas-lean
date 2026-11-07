# R.e. predicates are the halting sets of multi-stack machines

A predicate $p$ on
$\mathbb{N}$ is recursively enumerable if and only if there are a bundled finite multi-stack
Turing machine and an identification of its input alphabet with the booleans such that, for
every $n \in \mathbb{N}$, $p(n)$ holds if and only if the machine halts on the binary digits of
$n$ (least significant first, with $1$ read as true, $0$ as false and no leading zeros, so that
$0$ gives the empty word).
