# Query total search problems TFNP^dt, decision-tree formulations and the black-box classes

A **total query search problem** is a sequence $R=(R_n)$ of relations $R_n\subseteq\{0,1\}^n\times O_n$, $O_n$ finite, such that every $x$ has some $o$ with $(x,o)\in R_n$; inputs are accessed only through bit queries. $R\in\mathsf{TFNP}^{dt}$ if each $o\in O_n$ has a verifier decision tree $T_o$ of depth $\mathrm{poly}(\log n)$ with $T_o(x)=1$ iff $(x,o)\in R_n$.

For total search problems $R\subseteq\{0,1\}^n\times O$ and $S\subseteq\{0,1\}^m\times O'$, an **$S$-formulation** of $R$ consists of functions $f_i:\{0,1\}^n\to\{0,1\}$ ($i\in[m]$) and $g_o:\{0,1\}^n\to O$ ($o\in O'$) such that for every input $x$ and every $o\in O'$, $(x,g_o(x))\in R$ if and only if $(f(x),o)\in S$, where $f(x)=(f_1(x),\dots,f_m(x))$. Its depth $d$ is the maximum decision-tree depth of the $f_i$ and $g_o$, its complexity is $\log m+d$, and $S^{dt}(R)$ is the least complexity. For a canonical problem $S$, $S^{dt}=\{R:S^{dt}(R_n)=\mathrm{poly}(\log n)\}$. With the grid-encoded canonical problems PIGEON, SINK-OF-LINE, END-OF-LINE, SINK-OF-DAG, SINK-OF-POTENTIAL-LINE, END-OF-POTENTIAL-LINE and UNIQUE-EOPL (the last adds as a solution two active nodes in the same row) one obtains $\mathsf{PPP}^{dt}$, $\mathsf{PPADS}^{dt}$, $\mathsf{PPAD}^{dt}$, $\mathsf{PLS}^{dt}$, $\mathsf{SOPL}^{dt}$, $\mathsf{EOPL}^{dt}$, $\mathsf{UEOPL}^{dt}$. A separation $X^{dt}\not\subseteq Y^{dt}$ implies an oracle separation $X^{\mathcal O}\not\subseteq Y^{\mathcal O}$ of the white-box classes.

## Depends on

- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Separations in Proof Complexity and TFNP", FOCS (2022) and Journal of the ACM 71(4) (2024), arXiv:2205.02168.
