# Promise constraint satisfaction PCSP(A,B) for a pair of finite templates

Let $\mathbb{A},\mathbb{B}$ be finite structures over the same finite relational signature with $\mathbb{A}\to\mathbb{B}$. The **promise constraint satisfaction problem** $\mathrm{PCSP}(\mathbb{A},\mathbb{B})$ has two versions.

- **Decision**: given a finite structure $\mathbb{X}$, output YES if $\mathbb{X}\to\mathbb{A}$ and NO if $\mathbb{X}\not\to\mathbb{B}$; inputs satisfying neither (with $\mathbb{X}\to\mathbb{B}$ but $\mathbb{X}\not\to\mathbb{A}$) are excluded by the promise.
- **Search**: given $\mathbb{X}$ with $\mathbb{X}\to\mathbb{A}$, find a homomorphism $\mathbb{X}\to\mathbb{B}$.

The decision version reduces to the search version. $\mathrm{PCSP}(\mathbb{A},\mathbb{A})=\mathrm{CSP}(\mathbb{A})$. The **approximate graph colouring** problem is $\mathrm{PCSP}(\mathbb{K}_k,\mathbb{K}_c)$ for $3\le k\le c$: distinguish $k$-colourable graphs from graphs that are not $c$-colourable (or $c$-colour a $k$-colourable graph). Brakensiek and Guruswami observed that the complexity is governed by polymorphisms in the promise sense.

## Depends on

- [Finite relational templates and the homomorphism problem CSP(A)](../finite-domain-csp-dichotomy/finite-templates-and-csp-of-a.md)
- [GRAPH COLORING as a decision problem](../../graph-coloring-and-partitioning/graph-coloring/graph-coloring-dec.md)

## Sources

- Libor Barto, Jakub Bulín, Andrei Krokhin and Jakub Opršal, "Algebraic approach to promise constraint satisfaction", Journal of the ACM 68(4) (2021), arXiv:1811.00970.
- Joshua Brakensiek and Venkatesan Guruswami, "Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy", ECCC TR16-183 (2016), arXiv:1704.01937.
