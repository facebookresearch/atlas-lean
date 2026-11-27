# Membership in the Culik–Yu classes of cellular automata is undecidable

For one-dimensional cellular automata it is undecidable whether all finite configurations evolve to the quiescent configuration, and hence undecidable whether an automaton lies in each of the first three classes of the Culik–Yu formalization of Wolfram's classification, even when choosing only between the first two.

**Classes.** Let $A=(S,N,f)$ be a one-dimensional [cellular automaton](../cellular-automata-on-z-d.md) with global map $G$. A state $s$ is *stable* if $f(s,\dots,s)=s$; a configuration is *$s$-finite* if all but finitely many cells are in state $s$, and a distinguished stable state $q$ is the *quiescent* state, with *finite* configurations the $q$-finite ones (see [finite, periodic and Garden-of-Eden configurations](../finite-periodic-and-garden-of-eden-configurations.md)). A configuration $c$ *evolves to* $c'$ if $G^i(c)=c'$ for some $i\ge0$. Culik and Yu define:

- $A$ is in *Class One* if there is a stable state $s$ such that every $s$-finite configuration evolves to the homogeneous configuration of $s$;
- $A$ is in *Class Two* if there is a stable state $s$ such that every $s$-finite configuration has an ultimately periodic evolution $c,G(c),G^2(c),\dots$;
- $A$ is in *Class Three* if there is a stable state $s$ such that, for $s$-finite configurations $c_1,c_2$, it is decidable whether $c_1$ evolves to $c_2$;
- Class Four contains all cellular automata.

The classes form a hierarchy, each containing the previous one.

**Theorem (Culik and Yu).** For one-dimensional cellular automata:

1. it is undecidable whether all finite configurations of a given automaton evolve to the quiescent configuration (Theorem 5), and undecidable whether a given automaton is in Class One (Corollary 1);
2. it is undecidable whether a given automaton is in Class Two (Theorem 8), and whether a given automaton of Class Two is in Class One (Theorem 9);
3. it is undecidable whether a given automaton is in Class Three (Theorem 12).

The source notes that its results other than those on limit languages extend easily to cellular automata of higher dimension. A cellular automaton that simulates a universal Turing machine is not in Class Three (Theorem 10), and the product of two cellular automata lies in the higher of their two classes.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](../cellular-automata-on-z-d.md)
- [Finite, periodic and Garden-of-Eden configurations](../finite-periodic-and-garden-of-eden-configurations.md)

## Proof depends on

- [Emptiness is undecidable](../../../computability/emptiness-and-equivalence-problems-for-programs/not-tm2-decidable-empty.md)
- [The halting problem for single-tape Turing machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

Part 1 reduces the emptiness problem for Turing machines with one one-way infinite tape. Since a cellular automaton has no distinguished initial configurations, every encoding of an instantaneous description, reachable or not, may appear initially; the automaton built from a machine $M$ uses three tracks so that every segment either runs a correct simulation that checks the computation from the beginning or is erased to quiescence, and all finite configurations become quiescent exactly when $M$ accepts nothing. As a by-product, it is undecidable whether a Turing machine halts from every instantaneous description (Corollary 2). Part 2 reduces this problem: valid segments simulate $M$ from any description and expand, invalid ones are erased, so every finite configuration has an ultimately periodic evolution exactly when $M$ halts from every description. Part 3 runs a simulation of $M$ beside a universal Turing machine $U$, so that the automaton is in Class Three exactly when $M$ halts on the given input. A good expansion links pages for the emptiness problem of single-tape Turing machines, for the undecidability of halting from every instantaneous description, and for universal Turing machines; the pages linked above give the halting and emptiness problems for other machine models.

## Sources

- Karel Culik II and Sheng Yu, "Undecidability of CA classification schemes", *Complex Systems* 2(2), pp. 177–190, 1988; read in the open-access copy published by the journal ([PDF](https://wpmedia.wolfram.com/sites/13/2018/02/02-2-2.pdf)): the definitions of Section 2, Definitions 1–3, Theorem 5 and Corollaries 1 and 2, Theorems 8 and 9, Theorems 10 and 12, and the abstract.
