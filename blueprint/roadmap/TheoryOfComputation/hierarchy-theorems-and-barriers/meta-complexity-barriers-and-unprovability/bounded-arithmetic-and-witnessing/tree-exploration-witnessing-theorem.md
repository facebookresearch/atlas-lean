# Game-theoretic witnessing for sentences with arbitrarily many quantifiers

Li and Oliveira show that a universal bounded theory proves a bounded sentence with any number of quantifier alternations exactly when the truthifier has a winning strategy computed by terms, of constant length, in the tree exploration game of the sentence. This generalizes KPT witnessing beyond $\forall\exists\forall$ sentences.

Let $\mathcal{T}$ be a universal bounded theory with vocabulary $\mathcal{L}$ that is closed under if-then-else, and let

$$
\varphi(x) = \exists y_1 \le t_1(x)\ \forall x_1 \le s_1(x, y_1)\ \cdots\ \exists y_k \le t_k(x, y_1, x_1, \dots, x_{k-1})\ \forall x_k \le s_k(x, y_1, \dots, y_k)\ \phi(x, \vec{x}, \vec{y})
$$

with $\phi$ quantifier-free. In the evaluation game on a board $(\mathcal{M}, n_0)$, where $\mathcal{M} \models \mathcal{T}$ and $x = n_0$, the truthifier and the falsifier alternately choose values for $y_i$ and $x_i$ within the bounds, and the truthifier wins if $\phi$ holds in $\mathcal{M}$. In the tree exploration game the truthifier may at each move continue any current play, start a new play, or replay an earlier position differently, the falsifier answering in the corresponding play, and the truthifier wins once some root-to-node path of the game tree is a winning transcript. An $\mathcal{L}$-strategy of the truthifier is a sequence of $\mathcal{L}$-terms, each describing the truthifier's next move from the moves so far; a length-$\ell$ $\mathcal{L}$-strategy is a universal winning strategy if the truthifier wins within $\ell$ moves on every board $(\mathcal{M}, n_0)$ against every strategy of the falsifier, not necessarily an $\mathcal{L}$-strategy. Then $\mathcal{T} \vdash \forall x\, \varphi(x)$ if and only if there is a universal winning $\mathcal{L}$-strategy of length $O(1)$ for the truthifier in the tree exploration game of $\varphi(x)$.

## Proof sketch

When $\varphi$ is an $\exists\forall$-formula the evaluation game has one round, and the tree exploration game reduces to sequential repetition of it, which is the student–teacher game of the KPT theorem. Winning by exploration rather than in a single play mirrors non-constructive proofs by excluded middle. The "if" direction is the completeness theorem: a countermodel gives the falsifier a strategy that never loses. The "only if" direction applies Herbrand's theorem for universal theories, in its general form with strong $\vee$-expansions, to $\forall x\, \varphi(x)$ and reads a winning strategy off the witnessing substitution. Li and Oliveira derive the KPT theorem from this result, not conversely. In the unprovability application one fixes a falsifier strategy adapted to the lower-bound sentence.

## Depends on

None.

## Proof depends on

- [Completeness for arbitrary languages](../../../../Logic/first-order-logic/g-del-s-completeness-theorem/provable-of-models-general.md)
- [Soundness for theories](../../../../Logic/first-order-logic/first-order-natural-deduction/models.md)

## Informally uses

- [Herbrand's theorem](../../../../Logic/first-order-logic/herbrand-s-theorem.md)

## Sources

- Jiatu Li and Igor C. Oliveira, "Unprovability of Strong Complexity Lower Bounds in Bounded Arithmetic", *STOC* 2023, DOI 10.1145/3564246.3585144, arXiv:2305.15235v1 (Theorem 1.6, Game-Theoretic Witnessing Theorem, and the definition of universal winning strategies, Section 1.2; restated as Theorem 3.1 and proved via Herbrand's theorem in Appendix B.1).
