# Emptiness of deterministic recurrent incidence automata is undecidable

Recurrent incidence automata read strings made of center-foldable factors and pass a stack-like interface from factor to factor through finite-state transformations; their emptiness problem is undecidable already for deterministic layers, and so are containment and equivalence.

**Factors and folding.** Fix a partitioned alphabet $\Pi$ with left classes $\Sigma_{\mathrm{stand}}, \Sigma_{\mathrm{lean}}, \Sigma_{\mathrm{local}}$ and right classes $\Omega_{\mathrm{stand}}, \Omega_{\mathrm{lean}}, \Omega_{\mathrm{local}}$, with $\Sigma$ and $\Omega$ their unions, as in the partitioned alphabets of [visibly pushdown automata](visibly-pushdown-automata.md). The *center-foldable factors* are the words $x_1 \cdots x_n y_n \cdots y_1$ with $x_1 \in \Sigma_{\mathrm{local}}$, all $x_i \in \Sigma$, all $y_i \in \Omega$ and $y_1 \in \Omega_{\mathrm{local}}$; they form a prefix-free language $\nabla$, so every word of $\nabla^*$ splits uniquely into factors. Such a factor *folds* into the string of pairs $(x_1, y_1) \cdots (x_n, y_n)$ over $\Sigma \times \Omega$.

**Units and layers.** An *RIA unit* $A = (Q, I, F, \Pi, \Gamma, \delta)$ has finite sets of local states $Q$, initial states $I$ and final states $F \subseteq Q \setminus I$, a finite stack alphabet $\Gamma$, and transitions $(q, x, \gamma, \gamma', q')$ reading a pair $x$ and consuming $\gamma \in \Gamma \cup \{\varepsilon\}$ from an input interface while emitting $\gamma' \in \Gamma \cup \{\varepsilon\}$ to an output interface; pairs in $\Sigma_{\mathrm{local}} \times \Omega_{\mathrm{stand}}$ are calls (emit a symbol), in $\Sigma_{\mathrm{stand}} \times \Omega_{\mathrm{local}}$ returns (consume one), in $\Sigma_{\mathrm{lean}} \times \Omega_{\mathrm{lean}}$ replaces (rewrite one), in $\Sigma_{\mathrm{local}} \times \Omega_{\mathrm{local}}$ internal moves, and transitions from initial states carry the control state of the layer as a carrier symbol. An accepting computation on the folding of a factor $w$ from an initial to a final state turns an interface $\sigma = \gamma_1 \cdots \gamma_n \rho \in \Gamma^+$ into $\sigma' = \gamma'_1 \cdots \gamma'_n \rho$, the suffix $\rho$ untouched; this defines the stack-transformation relation $[\![A]\!]$, which is composed factor by factor. An *RIA layer* $\mathcal{A} = (A, G, H)$ adds sets $G, H \subseteq \Gamma$ of initial and final carrier symbols, and recognizes $L_{\mathcal{A}}$, the strings $w \in \nabla^*$ such that the composition of $[\![A]\!]$ along the factors of $w$ relates some one-symbol interface in $G$ to some one-symbol interface in $H$. The layer is *deterministic* if $G$ is a singleton and $A$ is functional, that is, $[\![A]\!]$ is a partial function from pairs of a factor and an input interface to output interfaces. Determinism is a semantic condition: the unit itself may be nondeterministic. $\mathsf{RIL}$ and $\mathsf{DRIL}$ denote the families of languages of layers and of deterministic layers. Layers are given as finite tuples, so each problem takes one or two layers as input; containment asks whether $L_{\mathcal{A}} \subseteq L_{\mathcal{B}}$ and equivalence whether $L_{\mathcal{A}} = L_{\mathcal{B}}$.

**Theorem (Yli-Jyrä).**

1. The emptiness problem is undecidable for deterministic RIA layers (Theorem 16 of the source).
2. Emptiness, containment and equivalence are undecidable for $\mathsf{DRIL}$ and for $\mathsf{RIL}$ (Corollary 17).

## Depends on

- [Visibly pushdown automata and visibly pushdown languages](visibly-pushdown-automata.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The halting problem for deterministic two-counter machines reduces to emptiness of deterministic layers: a machine configuration is stored as a string on the interface, the first factor writes the initial configuration, and each later factor applies one deterministic machine step as a functional stack transformation computed by the unit; on reaching the halting state the interface is reduced to a final carrier symbol, so the layer accepts some string exactly when the machine halts. Since the empty language is recognized by a deterministic layer, decidable containment or equivalence would decide emptiness, and $\mathsf{DRIL} \subseteq \mathsf{RIL}$ transfers the results.

## Sources

- A. Yli-Jyrä, "Recognizers for graph-encoding languages", *Electronic Proceedings in Theoretical Computer Science* 451, 2026, pp. 304–318, doi:10.4204/EPTCS.451.21; read in arXiv:2610.06743v1: the definitions of center-foldable factors and folding (Section 2), RIA units and layers (Section 3) and deterministic layers (Section 4), and the emptiness theorem and its corollary in Section 6, whose proofs are sketched in the source.
