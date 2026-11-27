# Barto–Kozik Absorption Theorem for linked subdirect products of Taylor algebras

For $R\subseteq A\times B$ call $a,a'\in A$ **$R$-linked** if there are $c_0=a,c_1,\dots,c_{2n}=a'$ with $(c_{2i},c_{2i+1})\in R$ and $(c_{2i+2},c_{2i+1})\in R$ for all $i < n$; $R$ is **linked** if any two elements of its first projection are $R$-linked, and $R$ is **subdirect**, $R\le_{sd}A\times B$, if both projections are onto. Let $\mathcal{V}$ be an idempotent locally finite variety. Then $\mathcal{V}$ is a Taylor variety if and only if: for all finite $\mathbf{A},\mathbf{B}\in\mathcal{V}$ and every linked subdirect subuniverse $R\le_{sd}\mathbf{A}\times\mathbf{B}$, either $R=A\times B$, or $\mathbf{A}$ has a proper absorbing subuniverse, or $\mathbf{B}$ has a proper absorbing subuniverse.

## Proof sketch

For the nontrivial direction take a counterexample $(R,\mathbf{A},\mathbf{B})$ with no proper absorbing subuniverses; replacing $R$ by an iterated composite $(R^{-1}\circ R)^{\circ k}$ one may assume $R^{-1}\circ R=A\times A$. One then studies the sets of common $R$-neighbours of subsets $X\subseteq A$; a maximal $X$ with a common neighbour, together with the Taylor term, produces a term operation absorbing the corresponding set of neighbours, contradicting minimality unless $R$ is full. The converse uses that a non-Taylor idempotent variety contains a two-element projection algebra, on which the "$\le$" order relation is linked, proper and subdirect without absorbing subuniverses.

## Depends on

- [Absorbing and binary absorbing subuniverses of a finite algebra](absorbing-and-binary-absorbing-subuniverses.md)
- [Weak near-unanimity, Taylor, Siggers and cyclic operations on a finite set](../finite-domain-csp-dichotomy/wnu-taylor-siggers-cyclic-operations.md)

## Proof depends on

- [Bulatov–Jeavons–Krokhin: a core with no Taylor polymorphism has an NP-complete CSP](../finite-domain-csp-dichotomy/bulatov-jeavons-krokhin-no-taylor-np-complete.md)

## Sources

- Libor Barto and Marcin Kozik, "Absorbing subalgebras, cyclic terms, and the constraint satisfaction problem", Logical Methods in Computer Science 8(1:07) (2012).
