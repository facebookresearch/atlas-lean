# Decision problems for Büchi tiling systems on infinite pictures are highly undecidable

For languages of infinite two-dimensional pictures recognized by Büchi tiling systems, nonemptiness is $\Sigma^1_1$-complete, while universality, and whether the language is recognized with the weaker "everywhere" or "somewhere" acceptance conditions, are $\Pi^1_2$-complete.

**Theorem.** Let $\Sigma$ be a finite alphabet and $\hat\Sigma = \Sigma \cup \{\#\}$. An *$\omega$-picture* over $\Sigma$ is a map $p : \omega \times \omega \to \hat\Sigma$ with $p(i, 0) = p(0, i) = \#$ for all $i$ and $p(i, j) \in \Sigma$ for $i, j > 0$. A *tiling system* $\mathcal A = (Q, \Sigma, \Delta)$ has a finite set $Q$ of states and a finite set $\Delta \subseteq (\hat\Sigma \times Q)^4$ of $2 \times 2$ tiles; a run on $p$ is a map $\rho : \omega \times \omega \to Q$ such that every $2 \times 2$ block of $p$ combined with $\rho$ is a tile of $\Delta$. For $F \subseteq Q$, the language *Büchi-recognized* (*A-recognized*, *E-recognized*) by $(\mathcal A, F)$ is the set of $\omega$-pictures having a run that visits $F$ at infinitely many positions (at every position, at some position). For an effective enumeration $(T_z)_{z \in \mathbb N}$ of Büchi tiling systems with Büchi-recognized languages $L_B(T_z)$:

1. $\{z : L_B(T_z) \ne \emptyset\}$ and $\{z : L_B(T_z)$ is infinite$\}$ are $\Sigma^1_1$-complete (Theorem 5.6 of the source);
2. $\{z : L_B(T_z) = \Sigma^{\omega,\omega}\}$ is $\Pi^1_2$-complete (Theorem 5.9), and inclusion and equivalence of such languages are $\Pi^1_2$-complete (Theorem 5.10);
3. $\{z : L_B(T_z)$ is E-recognizable$\}$ and $\{z : L_B(T_z)$ is A-recognizable$\}$ are $\Pi^1_2$-complete (Theorem 5.11).

Hence these problems lie at the first and second levels of the [analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md), far beyond the halting problem. Whether a Büchi-recognizable picture language is Büchi-recognized, or Muller-recognized, by a deterministic tiling system is also $\Pi^1_2$-complete (Theorem 5.13).

## Depends on

- [Analytical hierarchy](../../../degrees-and-hierarchies/analytical-hierarchy/analytical-hierarchy.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Membership follows by writing the problems as formulas: through a recursive bijection between $\omega$-words and $\omega$-pictures, $L_B(T_z) = \Sigma^{\omega,\omega}$ says "for every $\sigma$ there is a run $\rho$ that is Büchi accepting on the picture of $\sigma$", a $\Pi^1_2$ statement, and "$L_B(T_z)$ is E-recognizable" says "there is $y$ with $L_B(T_z) = L_E(T_y)$". Hardness transfers results of Castro and Cucker on $\omega$-languages accepted by Turing machines with Büchi acceptance: such languages are encoded into Büchi-recognizable picture languages by computable reductions (Lemmas 5.4, 5.5, 5.7 and 5.8), so that, for instance, universality of Büchi Turing machines, which is $\Pi^1_2$-complete, reduces to universality of Büchi tiling systems. For E- and A-recognizability, a machine $M_z$ is turned into a Büchi tiling system whose language is all pictures if $M_z$ is universal and is not a Borel set otherwise; since E-recognized picture languages are $\Sigma^0_2$ sets and A-recognized ones are closed, the language is E- (A-)recognizable iff $M_z$ is universal.

## Sources

- O. Finkel, "Highly Undecidable Problems about Recognizability by Tiling Systems", *Fundamenta Informaticae* 91(2):305–323, 2009, doi:[10.3233/FI-2009-0045](https://doi.org/10.3233/FI-2009-0045); read as arXiv:0811.3704v1, whose numbering is used here: Section 2 (pictures, tiling systems, Definition 2.1), Section 3 (analytical hierarchy), Lemmas 5.4, 5.5, 5.7 and 5.8, Theorems 5.6, 5.9, 5.10, 5.11 and 5.13.
