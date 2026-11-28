# Emptiness and universality of probabilistic limsup and liminf automata are undecidable

For probabilistic weighted automata on infinite words that value a run by the limsup or liminf of its weights, quantitative emptiness is undecidable for limsup under positive semantics and for liminf under almost-sure semantics, and quantitative universality is undecidable for limsup under positive semantics.

**Probabilistic weighted automata.** A *probabilistic weighted automaton* $A = \langle Q, \rho_I, \Sigma, \delta, \gamma \rangle$ has a finite set $Q$ of states, an initial distribution $\rho_I$ on $Q$, a finite alphabet $\Sigma$, a probabilistic transition function $\delta \colon Q \times \Sigma \to \mathcal{D}(Q)$ and a weight function $\gamma \colon Q \times \Sigma \times Q \to \mathbb{Q}$. On an infinite word $w$, the transition probabilities define a probability measure $\mathbb{P}^A$ on runs, and a run $r$ yields the weight sequence $\gamma(r) = v_0 v_1 \cdots$. For $\mathsf{LimSup}(v) = \limsup_n v_n$ and $\mathsf{LimInf}(v) = \liminf_n v_n$, a probabilistic $\mathsf{Val}$-automaton defines the quantitative languages

$$
L^{>0}_A(w) = \sup \{ \eta : \mathbb{P}^A(\{ r : \mathsf{Val}(\gamma(r)) \ge \eta \}) > 0 \}, \qquad
L^{=1}_A(w) = \sup \{ \eta : \mathbb{P}^A(\{ r : \mathsf{Val}(\gamma(r)) \ge \eta \}) = 1 \}
$$

(*positive* and *almost-sure* semantics). As inputs to the decision problems, automata are given by finite tables whose initial and transition probabilities and weights are rational numbers; the undecidability results come from probabilistic Büchi and co-Büchi automata with rational probabilities. Given such an automaton and a rational $\nu$, the *quantitative emptiness problem* asks whether some infinite word $w$ has $L_A(w) \ge \nu$, and the *quantitative universality problem* whether every infinite word $w$ has $L_A(w) \ge \nu$. Probabilistic Büchi and co-Büchi automata are the limsup and liminf automata with weights in $\{0, 1\}$.

**Theorem (Chatterjee, Doyen and Henzinger).**

1. Emptiness of probabilistic limsup automata under positive semantics is undecidable.
2. Emptiness of probabilistic liminf automata under almost-sure semantics and universality of probabilistic limsup automata under positive semantics are undecidable.

In contrast, emptiness of almost-sure limsup automata, universality of positive liminf automata and emptiness of positive liminf automata are decidable, as the same paper shows.

## Depends on

- [Büchi acceptance condition](../emptiness-of-b-chi-automata/mem-language-iff.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The source obtains both items as corollaries of undecidability results for probabilistic Büchi and co-Büchi automata on infinite words (emptiness under positive and almost-sure semantics); Büchi and co-Büchi automata are the special cases with weights $0$ and $1$. A good expansion links pages for those results.

## Sources

- K. Chatterjee, L. Doyen and T. A. Henzinger, "Probabilistic Weighted Automata", in *CONCUR 2009 – Concurrency Theory*, Lecture Notes in Computer Science 5710, Springer, 2009, pp. 244–258, doi:10.1007/978-3-642-04081-8_17; read as arXiv:0909.1647v1, <https://arxiv.org/abs/0909.1647v1>: Theorem 7, first clause (item 1), and Theorem 10 (item 2); the universality clause of Theorem 7 is left out because Theorem 9 of the same version states the opposite for the same class, the definitions of value functions, probabilistic weighted automata and the two semantics in Section 2, and the decidability theorems of Section 5, in the numbering of that version.
