# Fournier–Limaye–Malod–Srinivasan: the depth-four chasm is tight

Let $\mathrm{IMM}_{n,d}$ be the $(1,1)$ entry of the product of $d$ generic $n \times n$ matrices. Every homogeneous $\Sigma\Pi\Sigma\Pi^{[t]}$ circuit computing $\mathrm{IMM}_{n,d}$ with $t = \sqrt{d}$ and $d \le n^{c}$ for a small constant $c$ has size $n^{\Omega(\sqrt{d})}$. Since $\mathrm{IMM}_{n,d} \in \mathrm{VP}$ and the Agrawal-Vinay-Tavenas reduction gives circuits of size $n^{O(\sqrt{d})}$ with bottom fan-in $\sqrt{d}$, the depth-four reduction cannot be improved in the exponent for homogeneous circuits.

## Proof sketch

Use projected shifted partials with respect to a set of derivatives along carefully chosen paths of the layered graph underlying iterated matrix multiplication; the word structure ensures the derivatives behave like a design polynomial. The upper bound for products of low-degree polynomials then matches the lower bound up to constants in the exponent.

## Depends on

- [Agrawal–Vinay–Koiran–Tavenas reduction to depth four](../depth-reduction-and-chasms/agrawal-vinay-tavenas.md)
- [Homogeneous depth-four circuits with bounded bottom fan-in](../depth-reduction-and-chasms/homogeneous-depth-four.md)

## Proof depends on

- [Projected shifted partials and the Nisan–Wigderson design polynomial](projected-shifted-partials.md)
- [The depth-four chasm: strong depth-four bounds separate VP from VNP](../depth-reduction-and-chasms/depth-four-chasm-corollary.md)

## Sources

- H. Fournier, N. Limaye, G. Malod, S. Srinivasan, "Lower bounds for depth-4 formulas computing iterated matrix multiplication", SIAM Journal on Computing 44 (2015); STOC (2014).
