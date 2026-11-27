# Sensitivity of three-dimensional cellular automata is Σ⁰₃-hard

The set of three-dimensional cellular automata that are sensitive to initial conditions is $\Sigma^0_3$-hard, whereas for one-dimensional cellular automata sensitivity is a $\Pi^0_2$ property; so the complexity of sensitivity grows with the dimension.

Sensitivity to initial conditions of a [cellular automaton on $\mathbb{Z}^d$](../cellular-automata-on-z-d.md) is defined on the page on [sensitivity and equicontinuity classes](sensitivity-and-equicontinuity-classes-of-cellul.md): some $\varepsilon > 0$ is such that every configuration has arbitrarily close configurations whose orbits eventually differ by more than $\varepsilon$, for the product-topology metric. Automata are given by their finite state set, neighborhood and local rule, and $\mathcal{S}_{ens}$ denotes the set of sensitive ones, a subset of the natural numbers under a fixed computable coding, placed in the [arithmetical hierarchy](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md).

**Theorem (Sablik and Theyssier).**

1. For one-dimensional cellular automata, the set $\mathcal{S}_{ens}$ is $\Pi^0_2$.
2. For three-dimensional cellular automata, the set $\mathcal{S}_{ens}$ is $\Sigma^0_3$-hard.

Since a $\Sigma^0_3$-hard set is not $\Pi^0_2$, sensitivity is strictly more complex in dimension three than in dimension one.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](../cellular-automata-on-z-d.md)
- [Sensitivity and equicontinuity classes of cellular automata are recursively inseparable in every dimension above one](sensitivity-and-equicontinuity-classes-of-cellul.md)
- [The arithmetical class $\Sigma_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

- [The cofiniteness index set is Σ⁰₃-complete](../../../degrees-and-hierarchies/arithmetical-hierarchy/cofiniteness-index-set-is-sigma03-complete.md)

## Expansion

In dimension one an automaton of radius $r$ is sensitive exactly when it has no blocking word (a result of Kůrka), and "there is a word $u$ such that for all $t$ the central cells of all configurations with $u$ in their center agree for $t$ steps" is a $\Sigma^0_2$ predicate, so sensitivity is $\Pi^0_2$. In dimension three the proof reduces the cofiniteness index set, the Turing machines that halt on all but finitely many inputs, to $\mathcal{S}_{ens}$: from a machine $M_i$ one computes an automaton whose planes run the two-dimensional "onion" construction of the companion page, with simulations of $M_i$ on successive inputs, and a third coordinate that ties the planes together, so that the automaton has an equicontinuous point exactly when the simulations can run forever on infinitely many inputs. Sensitivity then holds exactly when $M_i$ halts on a cofinite set of inputs. A complete expansion links Kůrka's characterization of sensitive one-dimensional automata as those without blocking words, which has no page.

## Sources

- M. Sablik and G. Theyssier, "Topological dynamics of cellular automata: dimension matters", *Theory of Computing Systems* 48(3):693–714, 2011 (published online 2010), doi:10.1007/s00224-010-9255-x; read in arXiv:0811.2731v2: the two propositions of the section "Complexity of Sensitivity According to Dimension" (the $\Pi^0_2$ upper bound in dimension one and the $\Sigma^0_3$-hardness in dimension three) with their proofs.
