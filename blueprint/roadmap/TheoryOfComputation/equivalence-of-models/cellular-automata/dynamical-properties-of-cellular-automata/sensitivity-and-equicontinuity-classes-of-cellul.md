# Sensitivity and equicontinuity classes of cellular automata are recursively inseparable in every dimension above one

In every dimension $d \ge 2$, the cellular automata that have equicontinuous points, those that are sensitive to initial conditions, and those that are neither are three classes none of which is recursively enumerable or co-recursively enumerable, and any two of which are recursively inseparable.

Let $\mathcal{E}_{qu}$, $\mathcal{S}_{ens}$ and $\mathcal{N}$ be the classes of $d$-dimensional cellular automata with an equicontinuous point, sensitive to initial conditions, and neither, as defined in [sensitivity and equicontinuity of cellular automata](sensitivity-and-equicontinuity-of-cellular-automata.md). Automata are coded by natural numbers through their finite descriptions, so the classes are sets of numbers that may be [recursively enumerable](../../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md) or [co-recursively enumerable](../../../computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md). Two disjoint sets of automata are *recursively inseparable* if no decidable set contains one and is disjoint from the other.

**Theorem (Sablik and Theyssier).** For every dimension $d \ge 2$:

1. each of $\mathcal{E}_{qu}$, $\mathcal{S}_{ens}$ and $\mathcal{N}$ is neither recursively enumerable nor co-recursively enumerable;
2. any two of them are recursively inseparable.

For the complexity of sensitivity in dimensions one and three see the page on [sensitivity of three-dimensional cellular automata](sensitivity-of-three-dimensional-cellular-automa.md) for the jump in complexity with the dimension.

## Depends on

- [Sensitivity and equicontinuity of cellular automata](sensitivity-and-equicontinuity-of-cellular-automata.md)
- [Cellular automata on $\mathbb{Z}^d$](../cellular-automata-on-z-d.md)
- [Recognizability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Co-recognizability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The core construction turns a two-dimensional tile set $\tau$ into cellular automata whose dynamics are governed by whether $\tau$ tiles the plane: a solid phase that erodes along tiling errors spreads through a liquid phase, so that valid tilings yield configurations that block information flow. The paper builds three recursive maps: one whose image has no equicontinuous point and is sensitive exactly when $\tau$ does not tile the plane; one ("onion" construction) that is sensitive when $\tau$ does not tile and has equicontinuous points when it does; and a combination that is never sensitive and has equicontinuous points exactly when $\tau$ tiles. Since the tile sets that tile the plane form a co-recursively enumerable set that is not recursive, hence not recursively enumerable, each map transfers non-enumerability and inseparability to the corresponding pair of classes. The canonical lift of a $d$-dimensional automaton to dimension $d + 1$ preserves both properties, which extends the result from $d = 2$ to all $d \ge 2$.

## Sources

- M. Sablik and G. Theyssier, "Topological dynamics of cellular automata: dimension matters", *Theory of Computing Systems* 48(3):693–714, 2011 (published online 2010), doi:10.1007/s00224-010-9255-x; read in arXiv:0811.2731v2: the definitions of the Definitions section, Theorem 1 of the section "Topological Classification Revisited" with its three-part proof, and Proposition 1 (the canonical lift, which raises the dimension).
