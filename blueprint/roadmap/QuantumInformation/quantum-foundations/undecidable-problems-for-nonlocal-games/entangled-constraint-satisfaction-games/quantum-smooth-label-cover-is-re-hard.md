# Quantum smooth label cover is RE-hard

For every soundness $0 < s < 1$ and every smoothness parameter $J$ there is a parameter $R$ for which deciding whether a $J$-smooth label cover instance with label sets of sizes determined by $J$ and $R$ has quantum synchronous value 1 or less than $s$ is RE-hard, in contrast with quantum unique label cover, which is decidable efficiently.

**Smooth label cover.** An instance $(G, [n], [k], \Sigma)$ consists of a regular connected graph $G = (V, E)$, a label set $[n]$ and, for each edge $e = (v, w)$, a pair of maps $\pi_{ev}, \pi_{ew} : [n] \to [k]$; an edge is satisfied by labels $a, b \in [n]$ at $v, w$ if $\pi_{ev}(a) = \pi_{ew}(b)$. For a positive integer $J$, the instance is *$J$-smooth* if for every vertex $v$ and distinct labels $a \neq a'$ in $[n]$, a uniformly random neighbor $w$ of $v$, with $e = (v, w)$, satisfies $\pi_{ev}(a) = \pi_{ev}(a')$ with probability at most $1/J$: two labels at the same vertex rarely collide under the map of a random incident edge. A *quantum synchronous assignment* is a family of projection-valued measurements $\{P_v^a\}_{a \in [n]}$, $v \in V$, on one finite-dimensional Hilbert space, and its value is

$$
\omega_q^s(\mathfrak S, S) = \frac{1}{|E|} \sum_{e = (v, w) \in E} \ \sum_{i, j \in [n] : \pi_{ev}(i) = \pi_{ew}(j)} \operatorname{tr}(P_v^i P_w^j),
$$

with $\operatorname{tr}$ the normalized trace; the *quantum synchronous value* $\omega_q^s(\mathfrak S)$ of the instance $\mathfrak S$ is the supremum over all such assignments. It equals the synchronous quantum value of the associated two-player game, in which each player receives one endpoint of a random edge and answers a label. $\mathrm{SLC}_q(1, s)$ is the promise problem of deciding whether $\omega_q^s(\mathfrak S) = 1$ or $\omega_q^s(\mathfrak S) < s$.

**Theorem (Culf, Mastel, Paddock and Spirig).** For every $0 < s < 1$ and every positive integer $J$ there is a positive integer $R$ such that $\mathrm{SLC}_q(1, s)$ is RE-hard already on $J$-smooth instances with label sets $[n]$ and $[k]$ of sizes $n = 7^{(J+1)R}$ and $k = 2^R 7^{JR}$ (Theorem 10 of arXiv:2510.03477v3 and its proof). The proof gives one $R$ for all $J$: $R$ depends on $s$ alone. The same holds, for every $J$, for the oracularized value, the supremum over quantum assignments in which $P_v^a$ and $P_w^b$ commute for every edge $(v, w)$ (Corollary 18).

The instances produced by the reduction come from a $(J, R)$-dummy clause–variable game built from a 3SAT-5 instance; $R$ is chosen so that the value of the dummy game in the no case, which is at most an inverse exponential in $R$ independent of $J$ (Lemma 12 and Corollary 13 of the source, from parallel repetition), is below $s$, and Lemma 15 gives the smoothness for each $J$. Every instance is $1$-smooth, so the result is about large $J$. Their smoothness is the bound $1/J$ of Lemma 15 of the source, which compares two labels at the same vertex under the same map; the informal description of smoothness in Section 3 of the source, and the subscripts printed in its display (3.1), compare maps at the two endpoints instead. Edge satisfaction, by contrast, compares the maps at the two endpoints.

## Depends on

- [Finite simple graph](../../../../GraphTheory/planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Synchronous two-prover games](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/synchronous-two-prover-games.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Entangled 3SAT with every variable in five clauses is RE-hard](entangled-3sat-with-variable-degree-five-is-re.md)

## Expansion

The proof is a quantum analogue of the classical reduction of Khot and of Guruswami, Håstad, Manokaran, Raghavendra and Charikar. From a 3SAT-5 instance $B$ one builds the $(J, R)$-dummy clause–variable game, which asks $(J+1)R$ clauses to one player and, to the other, the same clauses with $R$ of them replaced by one of their variables; the players must answer consistently. If the clause–variable game of $B$ has value 1, so does this game; if its value is less than 1, then by the parallel repetition theorem for entangled projection games of Dinur, Steurer and Vidick the value drops below an inverse exponential in $R$. Khot's lemma on dummy clauses gives the smoothness, and the label cover instance is read off the connectivity graph of the game. A good expansion links the parallel repetition theorem for entangled projection games and Khot's smoothness lemma. By contrast, the quantum value of unique games can be approximated in polynomial time (Kempe, Regev and Toner).

## Sources

- E. Culf, K. Mastel, C. Paddock and T. Spirig, "The quantum smooth label cover problem is undecidable", in *53rd International Colloquium on Automata, Languages, and Programming (ICALP 2026)*, Leibniz International Proceedings in Informatics 374, Schloss Dagstuhl, 2026, article 71, pp. 71:1–71:23, doi:10.4230/LIPIcs.ICALP.2026.71; read as arXiv:2510.03477v3, <https://arxiv.org/abs/2510.03477v3>: Section 1, Section 3 (the definition of smooth label cover, quantum synchronous and oracularizable assignments, Definition 11 of the dummy clause–variable game, Lemma 12, Corollary 13, Definition 14, Lemma 15, Theorem 10 with its proof, Corollary 18).
