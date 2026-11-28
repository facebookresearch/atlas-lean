# Inclusion and equivalence of Petri net ω-languages are Π¹₂-complete

For infinite-word languages accepted by Petri nets, modeled as real-time Büchi automata with four blind counters, inclusion and equivalence are $\Pi^1_2$-complete, and whether such a language is Borel, or lies in a given Borel class, is $\Pi^1_2$-hard.

**Blind counter automata.** A *real-time $k$-counter machine* $\mathcal M=(K,\Sigma,\Delta,q_0)$ has a finite set $K$ of states, an input alphabet $\Sigma$, an initial state $q_0$ and transitions $\Delta\subseteq K\times\Sigma\times\{0,1\}^k\times K\times\{0,1,-1\}^k$: from a configuration $(q,c_1,\dots,c_k)$ with $c_i\in\mathbb N$, a transition $(q,a,i_1,\dots,i_k,q',j_1,\dots,j_k)$ reads $a$ when each $i_m$ records whether $c_m>0$, and adds $j_m$ to $c_m$, never decrementing a zero counter. A counter is *blind* (partially blind) if the machine cannot test it for zero: whenever a transition is enabled with that counter at $0$, the same transition is enabled with it positive. A *Büchi $k$-blind-counter automaton* adds accepting states $F\subseteq K$ and accepts the infinite words with a run from $(q_0,0,\dots,0)$ visiting $F$ infinitely often. A Petri net with labeled transitions is such an automaton: its unbounded places are the blind counters and its bounded places form the finite control.

**Theorem.** Let $(\mathcal P_z)_{z\in\mathbb N}$ be the source's Gödel numbering of all real-time Büchi $4$-blind-counter automata (Section 5 of the source; the hard instances read words over the alphabet $\Gamma = \Sigma \cup \{A, B, 0\}$ of Lemma 4.2, with $\Sigma$ the alphabet of the one-counter automata of Theorem 5.1, which has at least two letters). Then $\{(z,z') : L(\mathcal P_z)=L(\mathcal P_{z'})\}$ and $\{(z,z') : L(\mathcal P_z)\subseteq L(\mathcal P_{z'})\}$ are $\Pi^1_2$-complete (Theorem 6.1 of the source).

The source also shows that for every countable ordinal $\alpha\ge2$, the sets $\{z : L(\mathcal P_z)\in\boldsymbol\Sigma^0_\alpha\}$, $\{z : L(\mathcal P_z)\in\boldsymbol\Pi^0_\alpha\}$ and $\{z : L(\mathcal P_z)\text{ is Borel}\}$ are $\Pi^1_2$-hard (Theorem 5.2).

Hence these problems for $\omega$-languages of Petri nets lie far beyond the arithmetical hierarchy, at the second level of the [analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md).

## Depends on

- [Analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)
- [Place/transition Petri nets](../../../../ComputerScience/concurrent-systems-and-protocols/petri-nets/place-transition-petri-nets.md)
- [Büchi acceptance condition](../../emptiness-of-b-chi-automata/mem-language-iff.md)

## Proof depends on

- [Inclusion and equivalence of real-time Büchi one-counter automata are Π¹₂-complete](../omega-languages-of-one-counter-automata/inclusion-of-one-counter-omega-languages.md)

## Expansion

Membership in $\Pi^1_2$ holds already for $\omega$-languages of Turing machines. For hardness, the source's main construction simulates a real-time Büchi one-counter automaton $\mathcal A_z$, which may test its counter for zero, by a real-time Büchi $4$-blind-counter automaton: an injective computable $g$ gives $L(\mathcal P_{g(z)})=h(L(\mathcal A_z))\cup\mathcal L$, where $h$ is a computable coding onto an effective closed set and $\mathcal L$ is a fixed $\omega$-language, accepted by a real-time Büchi automaton with one blind counter, that is an arithmetical $\Sigma^0_1$ set. This coding preserves inclusion, equivalence and Borel classes from level $2$ on, so the $\Pi^1_2$-completeness of inclusion and equivalence for one-counter automata, and the $\Pi^1_2$-hardness of their Borel-class problems, transfer to Petri nets.

## Sources

- Olivier Finkel and Michał Skrzypczak, "On the Expressive Power of Non-deterministic and Unambiguous Petri Nets over Infinite Words", *Fundamenta Informaticae* 183(3–4), 2021, pp. 243–291, doi:[10.3233/FI-2021-2088](https://doi.org/10.3233/FI-2021-2088); read in arXiv:2107.04025v2 ([arXiv](https://arxiv.org/abs/2107.04025v2)), whose numbering is used: the introduction (Petri nets as partially blind multicounter automata), Section 2 (counter automata and blind counters), Theorem 5.2 and its proof, and Theorem 6.1 and its proof.
