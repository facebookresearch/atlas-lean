# Lipschitz robustness of deterministic transducers is undecidable

For every fixed constant $K > 0$, no algorithm decides whether a given deterministic finite-state transducer on finite words is $K$-Lipschitz robust with respect to given generalized Manhattan distances on its input and output words.

**Definitions.** A finite-state transducer $T$ (as in [rational relations and transducers](rational-relations-and-transducers.md)) reads an input word over $\Sigma$ and writes, on each transition, a finite word over $\Gamma$; it is *deterministic* if for each state and input letter at most one transition applies, and then it computes a partial function $[\![T]\!]$ on its domain $\mathrm{dom}(T) \subseteq \Sigma^*$. A *similarity function* on $\Sigma^*$ is a map $d : \Sigma^* \times \Sigma^* \to \mathbb{Q} \cup \{\infty\}$ with $d(s,t) \ge 0$ and $d(s,t) = d(t,s)$. A *generalized Manhattan distance* on finite words is

$$
d_M(s, t) = \sum_{i=1}^{\max(|s|, |t|)} \mathrm{diff}(s[i], t[i]),
$$

where the mismatch penalty $\mathrm{diff}$ is a distance on the alphabet extended by an end-of-word letter $\#$ (padding the shorter word) and may take the value $\infty$. Given $K \in \mathbb{Q}$ with $K > 0$ and similarity functions $d_\Sigma$ on $\Sigma^*$ and $d_\Gamma$ on $\Gamma^*$, a functional transducer $T$ is *$K$-Lipschitz robust* if

$$
d_\Sigma(s, t) < \infty \implies d_\Gamma([\![T]\!]\,(s), [\![T]\!]\,(t)) \le K \cdot d_\Sigma(s, t) \qquad \text{for all } s, t \in \mathrm{dom}(T).
$$

**Theorem.** It is undecidable, given a deterministic transducer $T$ on finite words and generalized Manhattan distances $d_\Sigma, d_\Gamma$, each given by its mismatch penalty as a finite table of nonnegative rationals and $\infty$, whether $T$ is $1$-Lipschitz robust with respect to $d_\Sigma, d_\Gamma$ (Theorem 10 of the source). Consequently, by scaling the output distance, for every fixed rational $K > 0$, $K$-Lipschitz robustness of deterministic transducers is undecidable.

The constant $K$ matters: for functional transducers on finite words and generalized Manhattan distances, whether some $K$ makes $T$ $K$-robust is decidable in co-NP (Proposition 11 of the source), and $K$-robustness of synchronized transducers, Mealy machines among them, is decidable in polynomial time when the distances are computed by functional weighted automata (Theorem 7). The same source shows that $K$-robustness of nondeterministic letter-to-letter transducers, measured with the Hausdorff or the inf-inf set-similarity function induced by an output distance, is undecidable even for generalized Manhattan distances.

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Reduce from the Post correspondence problem. Given pairs $(v_1, w_1), \dots, (v_k, w_k)$ over $\{a, b\}$, add the pair $(\diamond, \diamond)$, for a fresh letter $\diamond$, as number $k+1$, so that solutions ending with $k+1$ correspond to solutions of the original instance. The input letters are indices marked with a polarity $L$ or $R$; the deterministic transducer accepts words $\langle i_1, P\rangle \cdots \langle i_n, P\rangle \langle k+1, P\rangle$ of a single polarity $P$ and translates each $\langle i, L\rangle$ to $v_i$ and each $\langle i, R\rangle$ to $w_i$, every output letter marked with the polarity. The input distance is finite only between the $L$- and $R$-versions of the same index sequence, where it equals the total output length minus one; the output distance charges $2$ for equal letters of opposite polarity and $1$ for unequal letters or padding. A violation of $1$-robustness then occurs exactly when the two translations have equal length and equal underlying letters, that is, when the instance has a solution. Scaling the output distance by $K$ reduces $K$-robustness to $1$-robustness.

## Sources

- T. A. Henzinger, J. Otop and R. Samanta, "Lipschitz Robustness of Finite-state Transducers", in *34th International Conference on Foundation of Software Technology and Theoretical Computer Science (FSTTCS 2014)*, LIPIcs 29, pp. 431–443, 2014, doi:[10.4230/LIPIcs.FSTTCS.2014.431](https://doi.org/10.4230/LIPIcs.FSTTCS.2014.431). Read in arXiv:1404.6452v2 ([arXiv](https://arxiv.org/abs/1404.6452v2)), whose numbering is used here: the definitions of transducers, similarity functions and generalized Manhattan distances in Section 2, Definition 3 (K-Lipschitz robustness of functional transducers), Theorem 10 with its proof and the remarks after it, and Theorem 16 (nondeterministic letter-to-letter transducers).
