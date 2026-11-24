# Linear μ-calculus model checking on a finite Kripke structure

Let $E$ be a list of pairs of natural numbers (the edges), let $V$ be a valuation telling which
atoms hold at each world $w \in \mathbb{N}$, let $s$ be a natural number (the start world) and let
$\varphi$ be a linear μ-calculus formula with atoms in $\mathbb{N}$. The structure satisfies
$\varphi$ from $s$ when every infinite path $\pi : \mathbb{N} \to \mathbb{N}$ with $\pi(0) = s$
and $(\pi(t), \pi(t + 1)) \in E$ for every $t$ satisfies $\varphi$ at position $0$ of the word
whose atoms at position $t$ are those true at the world $\pi(t)$, in the empty environment
(every free fixpoint variable denotes the empty set of positions).
