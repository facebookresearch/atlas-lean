# Nontrivial properties of limit sets of binary cellular automata are undecidable

For one-dimensional cellular automata on two states, every property of the limit set that holds for some but not all nonsurjective
automata is undecidable; together with the decidability of surjectivity, surjectivity is, up to complement, the only decidable nontrivial limit set property.

Let $F : \{0, 1\}^{\mathbb{Z}} \to \{0, 1\}^{\mathbb{Z}}$ be a one-dimensional [cellular automaton](../cellular-automata-on-z-d.md) on two states. Its *limit set* is

$$
\Omega_F = \bigcap_{j \ge 0} F^j(\{0, 1\}^{\mathbb{Z}}),
$$

the set of configurations reachable arbitrarily late; $F$ is surjective exactly when $\Omega_F = \{0, 1\}^{\mathbb{Z}}$. A *property of limit sets* is a set $\mathcal{P}$ of subsets of $\{0, 1\}^{\mathbb{Z}}$, and
$F$ satisfies it when $\Omega_F \in \mathcal{P}$.

**Theorem.** Let $\mathcal{P}$ be a property of limit sets satisfied by the limit set of at least one nonsurjective cellular automaton on $\{0, 1\}$, but not by the limit sets of all of them.
Then it is undecidable, given a cellular automaton $F$ on $\{0, 1\}$ by its radius and the finite table of its local rule, whether $\Omega_F \in \mathcal{P}$ (Theorem 4.3 of the source).

Since surjectivity of one-dimensional cellular automata is decidable, surjectivity is, up to complement, the only nontrivial decidable property of limit sets of binary cellular
automata (the source's phrasing omits "up to complement"), and the same holds for every fixed alphabet with at least two letters. This refines Kari's Rice theorem for limit sets of cellular automata with arbitrary state sets.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](../cellular-automata-on-z-d.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Nilpotency of cellular automata is undecidable](../nilpotency-of-cellular-automata-is-undecidable.md)

## Expansion

A good expansion links a page for the undecidability of nilpotency for cellular automata with a spreading state (Theorem 2.2 of the source), which the proof reduces; the general nilpotency theorem does not give it, since the automata with a spreading state are a subclass. Given two nonsurjective binary automata $G_0$ and $G_1$ sharing a quiescent state,
with $\Omega_{G_0} \in \mathcal{P}$ and $\Omega_{G_1} \notin \mathcal{P}$, and an automaton $N$ with spreading state, it builds binary automata $F_0$ and $F_1$ with $\Omega_{F_i} = \Omega_{G_i}$ when $N$ is nilpotent and
$\Omega_{F_0} = \Omega_{F_1}$ otherwise. The construction simulates $N$ and a firing-squad automaton inside zones delimited by strongly freezing words, so that the binary alphabet
suffices. A decision procedure for $\mathcal{P}$ would then decide nilpotency of $N$.

## Sources

- P. Guillon and G. Richard, "Revisiting the Rice theorem of cellular automata", in *27th International Symposium on Theoretical Aspects of Computer Science (STACS 2010)*, LIPIcs 5, pp. 441–452, 2010, doi:10.4230/LIPIcs.STACS.2010.2474; read in arXiv:1001.0253v4: Theorem 4.3 of Section 4 (Rice Theorem) with Lemmas 4.1 and 4.2 and the remark after it, Definitions 1.1–1.3 of Section 1, Theorem 2.2 (nilpotency) of Section 2 and the binary simulation of Section 3, with the numbering of that version.
