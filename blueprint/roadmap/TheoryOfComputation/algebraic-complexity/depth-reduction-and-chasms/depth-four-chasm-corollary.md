# The depth-four chasm: strong depth-four bounds separate VP from VNP

Let $\{f_n\}$ be a family in $\mathrm{VNP}$ with $\deg f_n = d_n$ and $n^{\Omega(1)} \le d_n \le n^{O(1)}$. If every homogeneous $\Sigma\Pi^{[O(\sqrt{d_n})]}\Sigma\Pi^{[\sqrt{d_n}]}$ circuit computing $f_n$ has size $n^{\omega(\sqrt{d_n})}$, then $\{f_n\} \notin \mathrm{VP}$ and hence $\mathrm{VP} \ne \mathrm{VNP}$.

## Proof sketch

If $f_n$ had circuits of size $s = n^{O(1)}$, the reduction to depth four would give homogeneous depth-four circuits of size $s^{O(\sqrt{d_n})} = n^{O(\sqrt{d_n})}$ with bottom fan-in $\sqrt{d_n}$, contradicting the hypothesis.

## Depends on

- [Valiant's VP versus VNP conjecture](../valiant-s-vp-versus-vnp-conjecture.md)
- [Homogeneous depth-four circuits with bounded bottom fan-in](homogeneous-depth-four.md)

## Proof depends on

- [Agrawal–Vinay–Koiran–Tavenas reduction to depth four](agrawal-vinay-tavenas.md)

## Sources

- M. Agrawal, V. Vinay, "Arithmetic circuits: a chasm at depth four", FOCS (2008).
- P. Koiran, "Arithmetic circuits: the chasm at depth four gets wider", Theoretical Computer Science 448 (2012) 56-65.
- S. Tavenas, "Improved bounds for reduction to depth 4 and depth 3", Information and Computation 240 (2015) 2-11; MFCS (2013).
