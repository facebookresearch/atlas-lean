# Multi-head finite automata

A $k$-head finite automaton is a finite automaton whose $k$ read-only heads move independently over the input word between two
end markers; it is one-way if no head ever moves left, and deterministic if each situation allows at most one move.

Let $k \ge 1$. A *nondeterministic two-way $k$-head finite automaton* is a tuple
$M = \langle S, A, k, \delta, \rhd, \lhd, s_0, F \rangle$ with a finite set $S$ of states, an input alphabet $A$, end markers
$\rhd, \lhd \notin A$, an initial state $s_0 \in S$, a set $F \subseteq S$ of accepting states, and a partial transition function
$\delta$ from $S \times (A \cup \{\rhd, \lhd\})^k$ to subsets of $S \times \{-1, 0, 1\}^k$, such that no head moves left of
$\rhd$ or right of $\lhd$. On input $w = a_1 \cdots a_n$ the tape contains $\rhd w \lhd$; a configuration is $(w, s, p)$ with
$p \in \{0, \dots, n + 1\}^k$ the head positions, the initial configuration is $(w, s_0, (1, \dots, 1))$, and
$(w, s, p) \vdash (w, s', p + d)$ whenever $(s', d) \in \delta(s, (a_{p_1}, \dots, a_{p_k}))$, with $a_0 = \rhd$ and
$a_{n+1} = \lhd$. The automaton halts when $\delta$ is undefined, and

$$
L(M) = \{ w \in A^* : (w, s_0, (1, \dots, 1)) \vdash^* (w, s, p) \text{ with } s \in F \text{ and } M \text{ halting in } (w, s, p) \} .
$$

$M$ is *deterministic* if every value of $\delta$ is undefined or a singleton, and *one-way* if no head ever moves left. The
four classes are written $\mathrm{2NFA}(k)$, $\mathrm{2DFA}(k)$, $\mathrm{1NFA}(k)$ and $\mathrm{1DFA}(k)$, and
$\mathscr{L}(X)$ is the family of languages accepted by automata of class $X$.

One head gives exactly the regular languages. In the one-way case $k + 1$ heads accept strictly more than $k$ heads, both
deterministically and nondeterministically (Yao and Rivest); two-way multi-head automata characterize logarithmic space.

## Depends on

None.

## Proof depends on

None.

## Sources

- M. Holzer, M. Kutrib and A. Malcher, "Multi-head finite automata: characterizations, concepts and open problems", in *Complexity of Simple Programs (CSP 2008)*, Electronic Proceedings in Theoretical Computer Science 1, pp. 93–107, 2009, doi:10.4204/EPTCS.1.9; Section 2 of the version arXiv:0906.3051v1: Definition 1, the definitions of acceptance, determinism and one-way automata after it, and Theorem 2 (the head hierarchy).
