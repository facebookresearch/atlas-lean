# Göös–Kamath–Sotiraki–Zampetakis: CHEVALLEY-WITH-SYMMETRY_p is PPA_p-complete and constant-depth formulas suffice

For every prime $p$: (i) CHEVALLEY-WITH-SYMMETRY$_p$ is $\mathsf{PPA}_p$-complete; it is the first natural $\mathsf{PPA}_p$-complete problem for $p\ge3$. (ii) LONELY$_p$, BIPARTITE$_p$ and LEAF$_p$ remain $\mathsf{PPA}_p$-complete when their input circuits are restricted to constant-depth arithmetic formulas over $\mathbb F_p$ with $+$ and $\times$ gates. (iii) For a range of parameters $n,m$, the problems BIS$_p$ (find $x\in\{0,1\}^n\setminus\{0\}$ with $Ax\equiv0\pmod p$) and SIS$_p$ (find $x\in\{-1,0,1\}^n\setminus\{0\}$ with $Ax\equiv0\pmod p$) Karp-reduce to CHEVALLEY$_p$; for constant $q$ in that range SIS$_q$ lies in $\mathsf{PPA}_q\cap\mathsf{PPP}$, and SIS$_q$ is polynomial-time solvable when $q=2^k3^\ell$.

## Proof sketch

Membership: the Chevalley–Warning lemma shows $|\mathcal V_{\mathbf g}|\equiv0$ unless a max-degree monomial exists; the order-$p$ symmetry partitions $\mathcal V_{\mathbf g}\setminus\mathcal V_{\mathbf h}$ into orbits of size $p$; so $|\mathcal V_{(\mathbf g,\mathbf h)}|\equiv0\pmod p$, and the cancellation of monomials and orbits is implemented as a BIPARTITE$_p$ instance with locally computable neighbourhoods. Hardness: from a $\mathsf{PPA}_p$-complete instance one builds explicit systems $\mathbf g,\mathbf h$ and an order-$p$ symmetry $\sigma$ whose extra common zeros correspond to solutions of the instance. Part (ii) follows because CHEVALLEY-WITH-SYMMETRY$_p$ reduces back to LONELY$_p$ with depth-bounded formulas.

## Depends on

- [CHEVALLEY_p, GENERAL-CHEVALLEY_p and CHEVALLEY-WITH-SYMMETRY_p: explicit search problems from the Chevalley–Warning theorem](chevalley-search-problems.md)
- [The modular classes PPA_q via BIPARTITE_q and the Buss–Johnson operator & combining two classes](ppa-q-and-the-and-operator.md)

## Proof depends on

- [Chevalley–Warning lemma: the zero count mod p equals ± the number of max-degree monic monomials](chevalley-warning-counting-lemma.md)
- [PPA_q equals the &-combination of PPA_p over the primes p dividing q, and PPA_p is closed under Turing reductions](ppa-q-equals-and-of-ppa-p.md)

## Sources

- Mika Göös, Pritish Kamath, Katerina Sotiraki and Manolis Zampetakis, "On the Complexity of Modulo-q Arguments and the Chevalley–Warning Theorem", CCC (2020), arXiv:1912.04467.
