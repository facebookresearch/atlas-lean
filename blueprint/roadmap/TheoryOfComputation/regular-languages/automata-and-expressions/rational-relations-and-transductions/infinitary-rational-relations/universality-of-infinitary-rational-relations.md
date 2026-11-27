# Universality, inclusion and equivalence of infinitary rational relations are Π¹₂-complete

For relations between infinite words accepted by Büchi transducers, universality, cofiniteness, inclusion and equivalence are $\Pi^1_2$-complete, far above the first-level hardness that the reduction from Post's correspondence problem gives.

Let $(\mathcal T_z)_{z\in\mathbb N}$ be an effective enumeration of the Büchi transducers (two-tape Büchi automata) over the alphabet $\Omega'=\{a,b,E,A,B,F,0,C\}$ on both tapes, defining [infinitary rational relations](infinitary-rational-relations-and-omega-rational.md) $R(\mathcal T_z)\subseteq\Omega'^\omega\times\Omega'^\omega$.

**Theorem.** The following sets are $\Pi^1_2$-complete, with respect to the [analytical hierarchy](../../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md):
1. (universality) $\{z: R(\mathcal T_z)=\Omega'^\omega\times\Omega'^\omega\}$;
2. (cofiniteness) $\{z: R(\mathcal T_z)\text{ has finite complement}\}$;
3. (inclusion) $\{(y,z): R(\mathcal T_y)\subseteq R(\mathcal T_z)\}$;
4. (equivalence) $\{(y,z): R(\mathcal T_y)=R(\mathcal T_z)\}$.

The source also shows (Theorem 4.7) that deciding whether $R(\mathcal T_z)$ is synchronized rational, whether its complement is infinitary rational, whether it is accepted by a deterministic transducer and whether it is unambiguous are $\Pi^1_2$-complete.

## Depends on

- [Infinitary rational relations and ω-rational functions](infinitary-rational-relations-and-omega-rational.md)
- [Analytical hierarchy](../../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)

## Proof depends on

- [Universality of real-time Büchi one-counter automata is Π¹₂-complete](../../../../omega-automata-and-games/weighted-and-counter-omega-automata/omega-languages-of-one-counter-automata/universality-of-one-counter-omega-languages.md)

## Expansion

Membership is as for one-counter automata: each property is a universal quantifier over pairs of infinite words (and runs) followed by an existential quantifier over runs, with an arithmetical matrix. For hardness, a coding from the source's earlier work simulates real-time Büchi one-counter automata by Büchi transducers: with $h(x)=C\,0\,x(1)\,C\,0^2\,x(2)\,C\cdots$ and $\alpha=C\,0\,C\,0^2\,C\,0^3\cdots$, an injective computable $H'$ maps $\mathcal C_z$ to a transducer accepting $(h(L(\mathcal C_z))\cup h(\Omega^\omega)^-)\times\{\alpha\}\ \cup\ \Omega'^\omega\times(\Omega'^\omega\setminus\{\alpha\})$. Then $L(\mathcal C_z)=\Omega^\omega$ iff $R(\mathcal T_{H'(z)})$ is universal, and similarly for the other problems, so the $\Pi^1_2$-completeness of universality for one-counter automata transfers. Earlier proofs via Post's correspondence problem gave only $\Sigma^0_1$- or $\Pi^0_1$-hardness.

## Sources

- Olivier Finkel, "Highly Undecidable Problems For Infinite Computations", *RAIRO - Theoretical Informatics and Applications* 43(2), 2009, pp. 339–364, doi:[10.1051/ita/2009001](https://doi.org/10.1051/ita/2009001); read in arXiv:0901.0373v1 ([arXiv](https://arxiv.org/abs/0901.0373v1)), whose numbering is used: Section 4: Definition 4.1 (two-tape Büchi automata), Lemmas 4.2, 4.3 and 4.5, Proposition 4.4, Theorem 4.6 and its proof, and Theorem 4.7.
