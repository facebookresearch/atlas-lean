# Probabilistic automata and cut-point languages

A *probabilistic automaton* over a finite alphabet $A$ has a finite set $Q$ of states, an initial state $q_0$, a set $F \subseteq Q$ of accepting
states and, for each letter $a$, a stochastic $Q \times Q$ matrix $M_a$, whose row $s$ is the probability distribution of the next state after
reading $a$ in state $s$. The *acceptance probability* $P_{\mathcal{A}}(w)$ of a word $w = a_1 \cdots a_n$ is the probability of being in $F$ after
reading $w$ from $q_0$, that is, the sum over $t \in F$ of the entries $(M_{a_1} \cdots M_{a_n})_{q_0, t}$; the *value* of $\mathcal{A}$ is
$\sup_w P_{\mathcal{A}}(w)$. For a *cut-point* $0 \le \lambda < 1$, the cut-point language is $L_{\mathcal{A}}(\lambda) = \{w : P_{\mathcal{A}}(w) > \lambda\}$,
and a number $\lambda \in [0, 1]$ is an *isolated* cut-point if there is $\varepsilon > 0$ with $|P_{\mathcal{A}}(w) - \lambda| \ge \varepsilon$ for every word $w$. A probabilistic automaton is a
[weighted automaton](weighted-automata-over-a-semiring.md) over the real semiring whose acceptance probability is its behavior.

## Depends on

- [Weighted automata over a semiring](weighted-automata-over-a-semiring.md)

## Sources

- N. Fijalkow, H. Gimbert, E. Kelmendi and Y. Oualhadj, "Deciding the value 1 problem for probabilistic leaktight automata", *Logical Methods in Computer Science* 11(2), 2015, arXiv:1504.04136v2: Section 1.1, Definition 1.1 (probabilistic automata and acceptance probabilities) and Definition 1.2 (value), and Section 1.2 (isolated cut-points, after Rabin).
- M. O. Rabin, "Probabilistic automata", *Information and Control* 6, 1963: the abstract (probabilistic automata, cut-points and isolated cut-points).
- G. Rote, "Probabilistic finite automaton emptiness is undecidable for a fixed automaton", *50th International Symposium on Mathematical Foundations of Computer Science (MFCS 2025)*, LIPIcs 345, 2025, paper 86, doi:10.4230/LIPIcs.MFCS.2025.86: Section 1.1 (the transition matrices of a probabilistic automaton and acceptance with probability above the cut-point).
