# LTL model checking as a decision problem

LTL model checking is the decision problem that accepts a bitstring $x$ exactly when $x$
decodes, under the canonical bitstring encoding, to a tuple $(n, E, L, s, \tau)$ of a natural
number $n$, a list $E$ of pairs of natural numbers (the edges), a list $L$ of lists of natural
numbers, a natural number $s$ (the start world) and a token list $\tau$ that decodes to an LTL
formula $\varphi$ with atoms in $\mathbb{N}$, such that $s < n$, both entries of every edge are
less than $n$, every world $w < n$ has a successor $v < n$ with $(w, v) \in E$, and every
infinite path from $s$ in the [transition system](kripke-lts.md) with edges $E$ satisfies
$\varphi$, where the atoms true at a world $w$ are those listed in entry $w$ of $L$ (none when $w$
is at least the length of $L$). Bitstrings that do not decode in this way are rejected.
