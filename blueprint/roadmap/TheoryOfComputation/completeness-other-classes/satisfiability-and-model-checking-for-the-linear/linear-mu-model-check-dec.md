# Linear μ-calculus model checking as a decision problem

Linear μ-calculus model checking is the decision problem that accepts a bitstring $x$ exactly
when $x$ decodes, under the canonical bitstring encoding, to a tuple $(n, E, L, s, \tau)$ of a
natural number $n$, a list $E$ of pairs of natural numbers (the edges), a list $L$ of lists of
natural numbers, a natural number $s$ (the start world) and a token list $\tau$ that decodes to a
linear μ-calculus formula $\varphi$ with atoms in $\mathbb{N}$, such that $\varphi$ is closed,
$s < n$, both entries of every edge are less than $n$, every world $w < n$ has a successor
$v < n$ with $(w, v) \in E$ (so that no path ends in a deadlock), and the structure
[satisfies $\varphi$ from $s$](linear-mu-model-check.md), where the atoms true at a world $w$ are
those listed in entry $w$ of $L$ (none when $w$ is at least the length of $L$). Bitstrings that do
not decode in this way are rejected.
