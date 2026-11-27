# Korten: constructing a hard truth table is APEPP-complete under P^NP reductions

Fix $0<\varepsilon<1$. Let $\mathrm{HardTT}_\varepsilon$ be the problem: given $1^{2^n}$, output a truth table of length $2^n$ whose circuit complexity is at least $2^{\varepsilon n}$. Then $\mathrm{HardTT}_\varepsilon\in\mathrm{APEPP}$, and every problem in $\mathrm{APEPP}$ reduces to $\mathrm{HardTT}_\varepsilon$ by a deterministic polynomial-time reduction with an $\mathrm{NP}$ oracle. Truth tables of length $2^n$ with circuit complexity $2^n/(2n)$ are also in $\mathrm{APEPP}$. The reduction generalizes to oracle circuits: hard truth tables for $\Sigma^{\mathrm{P}}_i$-oracle circuits are complete for $\mathrm{APEPP}_{\Sigma^{\mathrm{P}}_i}$ under $\Delta^{\mathrm{P}}_{i+2}$ reductions.

Shannon's counting proof that hard functions exist is thus a universal probabilistic existence argument: derandomizing it derandomizes every probabilistic-method construction captured by $\mathrm{APEPP}$.

## Proof sketch

Membership: the map sending a description of a circuit of size $s$ to its truth table has fewer input bits than output bits, and any non-image is a hard truth table. Hardness reinterprets Jeřábek's bounded-arithmetic equivalence between the dual weak pigeonhole principle and the existence of hard functions: an Avoid instance with stretch $2n$ is composed along a GGM-style binary tree into a circuit whose outputs all have small circuit complexity, so a hard truth table is a non-image of the tree, and an $\mathrm{NP}$ oracle walks the tree back to a non-image of the original circuit.

## Depends on

- [The total function class TFΣ2P and the explicit-construction class APEPP](tfsigma2p-and-apepp.md)

## Proof depends on

- [Shannon: most Boolean functions need exponential circuits](../../../circuit-complexity/shannon-s-circuit-size-lower-bound/shannon-hard-function.md)

## Sources

- Oliver Korten, "The Hardest Explicit Construction", FOCS (2021), arXiv:2106.00875.
- Emil Jeřábek, "Dual weak pigeonhole principle, Boolean complexity, and derandomization", Annals of Pure and Applied Logic 129 (2004).
