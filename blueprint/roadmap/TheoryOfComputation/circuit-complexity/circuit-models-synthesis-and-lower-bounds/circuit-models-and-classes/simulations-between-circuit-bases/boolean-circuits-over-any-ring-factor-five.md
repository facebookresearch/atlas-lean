# Boolean circuits are simulated over any field with constant-factor overhead

Let $F$ be a field and represent the Boolean values $0,1$ by $0_F,1_F$. Every Boolean circuit can be transformed into an arithmetic circuit over $F$ (with constant, addition and multiplication gates) that agrees with it on every $0/1$-valued input, with at most a constant-factor blowup in size: AND becomes multiplication, $\mathrm{AND}(y,z)=y\cdot z$; OR becomes $y+z-y\cdot z$; and negation becomes $1-y$.

## Proof sketch

Replace each gate by the corresponding expression; the identities $y\cdot z=\mathrm{AND}(y,z)$, $y+z-yz=\mathrm{OR}(y,z)$ and $1-y=\neg y$ hold for $y,z\in\{0,1\}$, so by induction every gate of the new circuit carries the $0/1$ value of the corresponding Boolean gate. Derived here: the same substitution works verbatim over any ring $R$ with $1_R\ne 0_R$, writing $1+(-1)\cdot y$ and $(y+z)+(-1)\cdot(yz)$; each expression uses at most five arithmetic gates, constants included, so a De Morgan circuit with $s$ gates, $n$ inputs and $m$ outputs becomes an arithmetic circuit over $R$ with at most $5s$ gates that outputs the $0/1$ representations of all $m$ outputs.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)
- [Arithmetic circuit](../../../../algebraic-complexity/arithmetic-circuits/arithmetic-circuit.md)

## Sources

- Justin Thaler, "Proofs, Arguments, and Zero-Knowledge", Foundations and Trends in Privacy and Security 4(2–4), 2022 (Section 4.2, arithmetization of a Boolean formula; Section 6.3, footnote 76: any Boolean circuit can be transformed into an equivalent arithmetic circuit over any field, with at most a constant-factor blowup in size).
