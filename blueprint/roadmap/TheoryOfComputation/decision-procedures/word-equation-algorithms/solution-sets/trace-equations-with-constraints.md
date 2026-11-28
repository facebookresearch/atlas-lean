# Trace equations with recognizable constraints

A trace equation is a word equation interpreted in a free partially commutative monoid with involution, in which letters commute when they share no resource; a recognizable constraint restricts the values of the variables through a morphism to a finite monoid.

A resource alphabet is a pair $(\Gamma, \rho)$ of a finite alphabet $\Gamma$ and a map $\rho : \Gamma \to 2^{\mathcal{R}}$ into the subsets of a finite set $\mathcal{R}$ of resources. The resource monoid is the quotient

$$
M(\Gamma, \rho) = \Gamma^* / \{ ab = ba : \rho(a) \cap \rho(b) = \emptyset \},
$$

so distinct letters commute exactly when they share no resource; its elements are traces, and $\pi : \Gamma^* \to M(\Gamma, \rho)$ is the projection. With a single resource shared by all letters, $M(\Gamma, \rho) = \Gamma^*$. An involution on $M(\Gamma, \rho)$ is a bijection $x \mapsto \bar{x}$ with $\bar{\bar{x}} = x$ and $\overline{xy} = \bar{y}\,\bar{x}$, induced by an involution on $\Gamma$ with $\rho(\bar{a}) = \rho(a)$; morphisms of monoids with involution respect the involution.

An equation is a pair $(U, V)$ of words over $\Gamma = A \cup \mathcal{X}$, partitioned into constants $A$ and variables $\mathcal{X}$, both closed under the involution. A constraint is a morphism $\mu : M(\Gamma, \rho) \to N$ to a finite monoid $N$ with involution, where the elements of $N$ are represented by $O(\log |\Gamma|)$ bits, the operations of $N$ (multiplication, involution, equality) are performed in space $O(\log |\Gamma|)$, and their specification takes $O(|\Gamma| \log |\Gamma|)$ space. A solution of $(U, V, \mu)$ over $M(A, \rho)$ is a morphism $\sigma : M(A \cup \mathcal{X}, \rho) \to M(A, \rho)$ of monoids with involution that fixes every constant, with

$$
\sigma(U) = \sigma(V) \quad \text{and} \quad \mu(\sigma(X)) = \mu(X) \text{ for all } X \in \mathcal{X} ;
$$

values $\sigma(X)$ may be empty. The input size is $n = |UV| + |\Gamma|$.

## Depends on

- [Ordinary word equation](../../string-constraints-and-word-equations/ordinary-word-equations/word-eq.md)

## Proof depends on

None.

## Expansion

These are the conventions of the conference version; the journal version uses the same resource model with different technical conventions (nonempty resource sets for constants, morphisms that do not increase resources, admissible constraint monoids and its own size measure), which are not mixed in here. The resource formalism expresses every independence relation compatible with the involution: given an irreflexive symmetric relation $I \subseteq \Gamma \times \Gamma$ with dependence $D = (\Gamma \times \Gamma) \setminus I$ such that $(a, b) \in I$ if and only if $(\bar{a}, b) \in I$, take as resources the unordered pairs $\{[a], [b]\}$ of involution orbits $[a] = \{a, \bar{a}\}$ with $(a, b) \in D$ (including $\{[a]\}$), and let $\rho(a)$ be the set of such pairs containing $[a]$. Then $\rho(\bar{a}) = \rho(a)$, and $\rho(a) \cap \rho(b) \neq \emptyset$ exactly when $(a, b) \in D$, since a pair containing both $[a]$ and $[b]$ is $\{[a], [b]\}$. Taking for $\rho(a)$ the set of letters dependent on $a$, as written in the journal version, does not give the same independence: on a dependence path $a - b - c$ it makes $a$ and $c$ share the resource $b$.

## Sources

- Volker Diekert, Artur Jeż, Manfred Kufleitner, "Solutions of Word Equations over Partially Commutative Structures", ICALP 2016, LIPIcs 55, Article 127 (2016), https://doi.org/10.4230/LIPIcs.ICALP.2016.127, Section 2 ("Main result"): resource alphabets, resource monoids, involutions, equations, constraints, solutions and input size
- Volker Diekert, Artur Jeż, Manfred Kufleitner, Alexander Thumm, "Solutions of word equations over partially commutative structures", International Journal of Algebra and Computation (2026), https://doi.org/10.1142/S0218196726500402; read as arXiv:1603.02966v4, https://arxiv.org/abs/1603.02966v4, Section 1.4 ("Resource formalism for partial commutation"), and Definitions 18 and 20 with Example 19 (Section 5.1) for the journal conventions
