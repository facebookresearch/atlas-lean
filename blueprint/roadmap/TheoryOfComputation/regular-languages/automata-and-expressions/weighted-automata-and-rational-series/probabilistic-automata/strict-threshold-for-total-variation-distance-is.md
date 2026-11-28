# The strict threshold problem for total variation distance is undecidable

No algorithm decides whether the total variation distance between the word distributions of two labeled Markov chains exceeds a given rational threshold.

**Labeled Markov chains.** A *labeled Markov chain* (a hidden Markov model) is a tuple $\mathcal{M} = (Q, \Sigma, M, \eta)$ with a finite set $Q$ of states, a finite alphabet $\Sigma$, a map $M \colon \Sigma \to [0,1]^{Q \times Q}$ of transition matrices and an end-of-word vector $\eta \in [0,1]^Q$ such that $\eta + \sum_{a \in \Sigma} M(a)\mathbf{1} = \mathbf{1}$, where $\mathbf{1}$ is the all-ones column vector, and such that every state has a positive-probability path to some state $q$ with $\eta(q) > 0$. An initial distribution $\pi$ on $Q$ then defines a probability distribution on finite words by $\pi(a_1 \cdots a_n) = \pi\, M(a_1) \cdots M(a_n)\, \eta$. The *total variation distance* between two initial distributions is

$$
d(\pi_1, \pi_2) = \sup_{W \subseteq \Sigma^*} |\pi_1(W) - \pi_2(W)| .
$$

By Proposition 2 of the source, the supremum is attained by $W = \{w : \pi_1(w) \ge \pi_2(w)\}$ and $d(\pi_1, \pi_2) = \max_{W} (\pi_1(W) - \pi_2(W)) = \frac12 \sum_{w \in \Sigma^*} |\pi_1(w) - \pi_2(w)|$.

**Theorem (Kiefer).** The *strict threshold-distance problem*, which asks, given a labeled Markov chain with rational transition matrices and end-of-word vector, two rational initial distributions $\pi_1, \pi_2$ and a rational $\tau \in [0, 1]$, whether $d(\pi_1, \pi_2) > \tau$, is undecidable (Theorem 3 of the source).

Decidability of the non-strict version ($d(\pi_1, \pi_2) \ge \tau$) is open, as the source states. The distance can nevertheless be approximated to any given precision, and for acyclic chains both threshold problems are PP-complete.

## Depends on

- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../emptiness-problem-for-probabilistic-automata.md)

## Expansion

The proof reduces the emptiness problem for probabilistic automata: from a probabilistic automaton one builds a labeled Markov chain and two initial distributions whose total variation distance exceeds a threshold exactly when some word is accepted with probability greater than the cut-point.

## Sources

- S. Kiefer, "On Computing the Total Variation Distance of Hidden Markov Models", in *45th International Colloquium on Automata, Languages, and Programming (ICALP 2018)*, Leibniz International Proceedings in Informatics (LIPIcs) 107, 2018, paper 130, doi:10.4230/LIPIcs.ICALP.2018.130; read as arXiv:1804.06170v1, <https://arxiv.org/abs/1804.06170v1>: Theorem 3 (the strict threshold-distance problem is undecidable) with its proof, Definition 1 (labeled Markov chains) and Proposition 2 (the two expressions for the distance) in Section 2, the definition of the threshold problems, the open non-strict case and the PP-completeness for acyclic chains (Theorem 7) in Section 3, and the approximation results of Section 4, in the numbering of that version.
