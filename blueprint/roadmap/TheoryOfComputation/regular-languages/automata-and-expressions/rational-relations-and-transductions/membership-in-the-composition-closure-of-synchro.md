# Membership in the composition closure of synchronous subsequential relations is undecidable

No algorithm decides, given finitely many synchronous subsequential relations on words and a pair of words, whether some finite composition of the relations relates the pair; equivalently, reachability, and hence emptiness, universality and inclusion, are undecidable for automata whose letters act by such relations.

**Synchronous subsequential relations.** Fix a finite alphabet $\Omega$ containing a designated letter $\square$. For an infinite word $\bar{x} \in \Omega^\omega$ let $\eta(\bar{x})$ be the finite word obtained by deleting a final segment $\square\square\square\cdots$ if $\bar{x}$ ends in one, and $\eta(\bar{x}) = \bar{x}$ otherwise. Let $T = (Q, \delta, \Omega, q_0)$ be an $\varepsilon$-free [transducer](rational-relations-and-transducers.md) without accepting states whose transitions $\delta \subseteq Q \times \Omega \times \Omega \times Q$ read one input letter and write one output letter, and which is total in the input; $L^\omega(T)$ is the set of pairs $(a_1a_2\cdots, b_1b_2\cdots)$ of infinite words labeling an infinite run from $q_0$. $T$ is *synchronous subsequential* if, whenever $(\bar{w}, \bar{v}) \in L^\omega(T)$ and $\eta(\bar{w})$ is finite, $\eta(\bar{v})$ is finite too. Its relation is $\{(\eta(\bar{w}), \eta(\bar{v})) : (\bar{w}, \bar{v}) \in L^\omega(T),\ \eta(\bar{w}) \in \Omega^*\} \subseteq \Omega^* \times \Omega^*$, and $\mathrm{SyS}$ is the class of relations so obtained; it is closed under composition.

**Closures and automata.** For relations $R_1, \dots, R_k \subseteq \Omega^* \times \Omega^*$ let $\{R_1, \dots, R_k\}^{\oplus}$ be the union of all finite compositions $R_{i_1} \circ \cdots \circ R_{i_m}$, $m \ge 0$, the empty composition being the identity of $\Omega^*$. A *self-constructing automaton* $\langle \Sigma, \phi, F \rangle$ has a finite alphabet $\Sigma$, a map $\phi$ sending each letter to a relation, extended to words by composition with $\phi(\varepsilon)$ the identity, and an accepting relation $F$; it accepts $w \in \Sigma^*$ when $\phi(w) \cap F \ne \emptyset$. Its *reachability problem* asks, given the automaton and a pair $(x, y)$, whether $(x, y) \in \phi(w)$ for some $w$.

**Theorem (Wurm).**

1. Given $R_1, \dots, R_k \in \mathrm{SyS}$, each by a synchronous subsequential transducer, and $(x, y) \in \Omega^* \times \Omega^*$, it is undecidable whether $(x, y) \in \{R_1, \dots, R_k\}^{\oplus}$. Equivalently, the reachability problem is undecidable for self-constructing automata whose letters act by relations in $\mathrm{SyS}$.
2. For self-constructing automata whose letters act by relations in $\mathrm{SyS}$ and whose accepting relation is finite, the emptiness, universality and inclusion problems are undecidable.

## Depends on

- [Rational relations and transducers](rational-relations-and-transducers.md)

## Proof depends on

- [PCP many-one reduces to nonemptiness of the intersection of two context-free languages](../../../undecidable-problems/intersection-problem-for-context-free-languages/many-one-reducible-pcp-inter.md)
- [The Post correspondence problem is undecidable](../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

With finite accepting relations, emptiness of such automata, reachability, and recursiveness of every relation $\{R_1, \dots, R_k\}^{\oplus}$ are equivalent. The paper encodes a pushdown automaton accepting by empty stack as an automaton over $\mathrm{SyS}$ relations with a finite accepting relation, the stack being kept in the word, and shows that two such encodings can be combined to recognize the intersection of the two context-free languages. Decidable emptiness would then decide emptiness of the intersection of two context-free languages, which is undecidable because the Post correspondence problem reduces to it. Inclusion and universality reduce emptiness.

## Sources

- C. Wurm, "Synchronous subsequentiality and approximations to undecidable problems", *Electronic Proceedings in Theoretical Computer Science* 193, 2015, pp. 58–72, doi:10.4204/EPTCS.193.5; read in arXiv:1509.07200v1: the definitions of relation automata, $\{\cdot\}^{\oplus}$ and synchronous subsequential transducers in Sections 2 and 3, Lemma 1 relating emptiness, reachability and recursiveness, Lemma 8 on context-free languages, and Theorem 9 with Corollary 10 in Section 4, in the numbering of that version.
