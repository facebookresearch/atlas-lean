# Weighted tree automata over strong bimonoids

A weighted tree automaton over a strong bimonoid assigns to each tree a weight computed bottom-up from transition weights;
strong bimonoids are like semirings but without distributivity, so initial algebra and run semantics can differ.

**Strong bimonoids.** A *strong bimonoid* is an algebra $(B, \oplus, \otimes, \mathbb{0}, \mathbb{1})$ such that
$(B, \oplus, \mathbb{0})$ is a commutative monoid, $(B, \otimes, \mathbb{1})$ is a monoid, $\mathbb{0} \ne \mathbb{1}$, and
$b \otimes \mathbb{0} = \mathbb{0} \otimes b = \mathbb{0}$ for all $b$. It is *computable* if $B$ is a recursive set and
$\oplus$, $\otimes$ are computable.

**Automata.** Let $\Sigma$ be a ranked alphabet, $\Sigma^{(k)}$ its symbols of rank $k$ and $T_\Sigma$ the set of trees over
$\Sigma$. A *$(\Sigma, B)$-weighted tree automaton* (wta) is $\mathcal{A} = (Q, \delta, F)$ with a finite nonempty set $Q$ of
states, transition maps $\delta_k : Q^k \times \Sigma^{(k)} \times Q \to B$ and a root weight vector $F : Q \to B$. It is
*bottom-up deterministic* if for all $k$, $\sigma \in \Sigma^{(k)}$ and $q_1, \dots, q_k$ at most one $q$ has
$\delta_k(q_1 \cdots q_k, \sigma, q) \ne \mathbb{0}$, and *crisp-deterministic* if moreover exactly one $q$ has
$\delta_k(q_1 \cdots q_k, \sigma, q) = \mathbb{1}$ and all other values are $\mathbb{0}$.

**Initial algebra semantics.** The vector algebra of $\mathcal{A}$ has carrier $B^Q$ and operations

$$
\delta_{\mathcal{A}}(\sigma)(v_1, \dots, v_k)_q = \bigoplus_{q_1, \dots, q_k \in Q} \Bigl(\bigotimes_{i=1}^{k} (v_i)_{q_i}\Bigr) \otimes \delta_k(q_1 \cdots q_k, \sigma, q),
$$

and $h_{\mathcal{A}} : T_\Sigma \to B^Q$ is the unique homomorphism from the term algebra. The *initial algebra semantics* is
$[\![\mathcal{A}]\!]^{\mathrm{i}}(\xi) = \bigoplus_{q \in Q} h_{\mathcal{A}}(\xi)_q \otimes F_q$, and two wta are *i-equivalent* if
their initial algebra semantics coincide. The *run semantics* $[\![\mathcal{A}]\!]^{\mathrm{r}}$ instead sums, over all runs, the
products of the transition weights along the run times the root weight; both semantics agree for bottom-up deterministic wta
and for wta over semirings.

Weighted string automata over $B$ are wta over monadic ranked alphabets (one symbol of rank $0$, the others of rank $1$).

## Depends on

- [Bottom-up finite tree automata](../../../../omega-automata-and-games/logic-and-tree-automata/bottom-up-finite-tree-automata.md)

## Proof depends on

None.

## Expansion

A crisp-deterministic wta computes a *recognizable step mapping*: a weighted tree language with finitely many values, each
taken on a recognizable tree language; the source proves that crisp-deterministic wta recognize exactly these. Finiteness of
the Nerode algebra of $\mathcal{A}$ implies that a crisp-deterministic wta i-equivalent to $\mathcal{A}$ exists.

## Sources

- Z. Fülöp, D. Kószó, H. Vogler, "Crisp-determinization of weighted tree automata over strong bimonoids", *Discrete Mathematics & Theoretical Computer Science* 23(1), article 5943, 2021, doi:[10.46298/dmtcs.5943](https://doi.org/10.46298/dmtcs.5943). Numbering of the version read, arXiv:1912.02660v3: Section 2.3 (strong bimonoids), Section 3.1 (wta, bottom-up deterministic and crisp-deterministic wta, initial algebra and run semantics), Section 8 (computable strong bimonoids) and Section 8.5 (string automata as wta over monadic alphabets).
