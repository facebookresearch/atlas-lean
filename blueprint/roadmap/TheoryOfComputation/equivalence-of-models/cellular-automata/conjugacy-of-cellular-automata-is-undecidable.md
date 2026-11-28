# Conjugacy of cellular automata is undecidable

It is undecidable whether two given one-dimensional cellular automata are topologically conjugate, whether the first is a factor of the second, and whether the first embeds into the second, already for one-sided automata, and the same holds for reversible two-dimensional automata.

**Theorem.** Let $\mathbb M = \mathbb N$ or $\mathbb M = \mathbb Z$, and consider [cellular automata](cellular-automata-on-z-d.md) $F : A^{\mathbb M} \to A^{\mathbb M}$ and $G : B^{\mathbb M} \to B^{\mathbb M}$ as dynamical systems. For $\mathbb M=\mathbb N$ these are *one-sided* automata, defined as on the linked page but on configurations indexed by $\mathbb N$ with a neighborhood $\{0,1,\dots,r\}$, so that $F(c)_i=f(c_i,\dots,c_{i+r})$; an instance is the finite local rule. A *homomorphism* from $(A^{\mathbb M}, F)$ to $(B^{\mathbb M}, G)$ is a continuous map $H$ with $H \circ F = G \circ H$; it is a *factor map* if surjective, an *embedding* if injective and a *conjugacy* if bijective, and it is *strong* if it also commutes with the shift. There is no algorithm that decides, given two cellular automata $F$ and $G$ on $A^{\mathbb M}$:

1. whether $F$ and $G$ are conjugate, or strongly conjugate;
2. whether $F$ is a factor, or a strong factor, of $G$;
3. whether $F$ is a subsystem, or a strong subsystem, of $G$, that is, whether $F$ embeds into $G$ by a homomorphism, or a strong one.

The same three statements hold for reversible cellular automata on $A^{\mathbb Z^2}$ (Corollary 2 of the source). In contrast, conjugacy is decidable for periodic cellular automata on one- or two-sided subshifts of finite type (Theorem 3 of the source, recalled from earlier work) and for positively expansive cellular automata on one- or two-sided full shifts (Proposition 7).

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](cellular-automata-on-z-d.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Nilpotency of cellular automata is undecidable](nilpotency-of-cellular-automata-is-undecidable.md)

## Expansion

The proof reduces nilpotency of one-sided one-dimensional cellular automata $H$ of radius $1$ with a spreading quiescent state, which is undecidable (Kari; Lewis). Combining $H$ with a fixed one-sided cellular automaton of positive entropy built for this purpose, one constructs $F$ and $G$ such that $F$ has strictly higher topological entropy than $G$ if $H$ is not nilpotent, while $F$ and $G$ are strongly conjugate, both of entropy zero, if $H$ is nilpotent. So these two sets of pairs are recursively inseparable (Theorem 2). Since a factor or a subsystem has entropy at most that of the system (Proposition 1 of the source), so that $F$ being a factor of $G$, or $F$ embedding into $G$, forces $h(F)\le h(G)$, which fails when $h(F)>h(G)$, any decision procedure for the three relations would separate them. A construction with acyclic orientations of $\mathbb Z^2$, based on Kari's undecidable infinite-path problem, gives the two-dimensional reversible case (Theorem 4). A good expansion adds pages for the undecidability of nilpotency for one-sided automata of radius $1$ with a spreading quiescent state (Kari; Lewis), for the fact that a factor or a subsystem has topological entropy at most that of the system, and for Kari's undecidable infinite-path problem used in Theorem 4.

## Sources

- J. Jalonen and J. Kari, "On the conjugacy problem of cellular automata", *Information and Computation* 274, 2020, article 104531, doi:[10.1016/j.ic.2020.104531](https://doi.org/10.1016/j.ic.2020.104531); read as arXiv:1906.00796v1, whose numbering is used here: Section 2 (homomorphisms, factors, subsystems, conjugacy), Theorem 1, Theorem 2 with its proof, Corollary 1, Theorem 3, Proposition 7, Proposition 9, Theorem 4 and Corollary 2.
