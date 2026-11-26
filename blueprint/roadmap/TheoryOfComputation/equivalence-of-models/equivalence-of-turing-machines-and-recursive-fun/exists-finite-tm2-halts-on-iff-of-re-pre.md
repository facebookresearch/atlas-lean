# Every r.e. predicate is the halting set of a machine with finite alphabets

For every
recursively enumerable predicate $p$ on $\mathbb{N}$ there are a bundled finite multi-stack Turing
machine whose stack alphabets are all finite and an identification of its input alphabet with
the booleans such that, for every $n \in \mathbb{N}$, $p(n)$ holds if and only if the machine
halts on the binary digits of $n$ (least significant first, with $1$ read as true, $0$ as false
and no leading zeros, so that $0$ gives the empty word).
