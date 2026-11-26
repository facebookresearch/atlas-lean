# Probabilistic automata and cut-point languages

A *probabilistic automaton* over a finite alphabet $A$ has a finite set $Q$ of states, an initial state $q_0$, a set $F \subseteq Q$ of accepting
states and, for each letter $a$, a stochastic $Q \times Q$ matrix $M_a$, whose row $s$ is the probability distribution of the next state after
reading $a$ in state $s$. The *acceptance probability* $P_{\mathcal{A}}(w)$ of a word $w = a_1 \cdots a_n$ is the probability of being in $F$ after
reading $w$ from $q_0$, that is, the sum over $t \in F$ of the entries $(M_{a_1} \cdots M_{a_n})_{q_0, t}$; the *value* of $\mathcal{A}$ is
$\sup_w P_{\mathcal{A}}(w)$. For a *cut-point* $0 \le \lambda \le 1$, the cut-point language is $L_{\mathcal{A}}(\lambda) = \{w : P_{\mathcal{A}}(w) \ge \lambda\}$,
and $\lambda$ is *isolated* if there is $\varepsilon > 0$ with $|P_{\mathcal{A}}(w) - \lambda| \ge \varepsilon$ for every word $w$. A probabilistic automaton is a
[weighted automaton](weighted-automata-over-a-semiring.md) over the real semiring whose acceptance probability is its behavior.

## Depends on

- [Weighted automata over a semiring](weighted-automata-over-a-semiring.md)

## Sources

- H. Gimbert and Y. Oualhadj, "Probabilistic automata on finite words: decidable and undecidable problems", *Proceedings of ICALP 2010*, Lecture Notes in Computer Science 6199, Springer, 2010 (version <https://hal.science/hal-00456538v2>): Section 1 (probabilistic automata, Definition 1), Section 2 (Rabin's cut-point languages) and Section 3, Definition 3 (isolated cut-points).
- M. O. Rabin, "Probabilistic automata", *Information and Control* 6, 1963: the abstract (probabilistic automata, cut-points and isolated cut-points).
