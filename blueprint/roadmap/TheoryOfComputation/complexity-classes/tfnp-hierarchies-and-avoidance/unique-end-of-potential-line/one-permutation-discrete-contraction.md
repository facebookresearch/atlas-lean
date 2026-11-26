# One-Permutation Discrete Contraction (OPDC): direction functions on a grid with unique fixpoints on i-slices

For widths $(k_1,\dots,k_d)$ let $P=\{0,\dots,k_1\}\times\dots\times\{0,\dots,k_d\}$, and let circuits $D_i:P\to\{\mathrm{up},\mathrm{down},\mathrm{zero}\}$ be given (discretising $f$ via $D_i(p)=\mathrm{up}$ iff $f(p)_i>p_i$, etc.). A **slice** fixes some coordinates; an **$i$-slice** fixes exactly the coordinates $j>i$. A point $p$ of slice $s$ is a fixpoint of $s$ if $D_j(p)=\mathrm{zero}$ for all free $j$. $(P,\mathcal D)$ is a one-permutation discrete contraction map if every $i$-slice $s$ has a unique fixpoint $q$, and whenever $p$ is the unique fixpoint of the sub-slice fixing free coordinate $i$, then $p_i<q_i\Rightarrow D_i(p)=\mathrm{up}$ and $p_i>q_i\Rightarrow D_i(p)=\mathrm{down}$.

**OPDC.** Output one of: (O1) $p$ with $D_i(p)=\mathrm{zero}$ for all $i$; (OV1) an $i$-slice and $p\ne q$ in it with $D_j(p)=D_j(q)=\mathrm{zero}$ for all $j\le i$; (OV2) an $i$-slice and $p,q$ in it, fixpoints of their $(i-1)$-slices, with $p_i=q_i+1$, $D_i(p)=\mathrm{down}$, $D_i(q)=\mathrm{up}$; (OV3) a fixpoint $p$ of its $(i-1)$-slice with $p_i=0$ and $D_i(p)=\mathrm{down}$, or $p_i=k_i$ and $D_i(p)=\mathrm{up}$. On the hypercube $\{0,1\}^n$ the direction functions orient the cube, and the slice condition is the unique-sink condition imposed only on the faces that are $i$-slices.

## Depends on

- [UNIQUE-EOPL, the class UEOPL and PromiseUEOPL: one potential line certified by violation solutions](unique-eopl-and-ueopl.md)

## Sources

- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", ICALP (2019), arXiv:1811.03841.
