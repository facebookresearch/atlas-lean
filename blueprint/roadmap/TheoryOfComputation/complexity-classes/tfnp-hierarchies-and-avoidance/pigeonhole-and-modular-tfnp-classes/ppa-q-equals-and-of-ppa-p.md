# PPA_q equals the &-combination of PPA_p over the primes p dividing q, and PPA_p is closed under Turing reductions

For every integer $q\ge2$,

$$
\mathsf{PPA}_q=\mathop{\&}_{p\ \mathrm{prime},\ p\mid q}\mathsf{PPA}_p .
$$

In particular $\mathsf{PPA}_{p^k}=\mathsf{PPA}_p$ for every prime power, a total-search analogue of the Beigel–Gill collapse $\mathrm{Mod}_{p^k}\mathsf P=\mathrm{Mod}_p\mathsf P$. Moreover $\mathsf{FP}^{\mathsf{PPA}_p}=\mathsf{PPA}_p$ for every prime $p$, $\mathsf{PPAD}\subseteq\mathsf{PPA}_q$ for every $q$, and for $q$ not a prime power $\mathsf{PPA}_q$ is not closed under black-box Turing reductions.

## Proof sketch

For $p\mid q$, replicating every edge of a BIPARTITE$_p$ instance $q/p$ times multiplies degrees by $q/p$, and $d\,q/p\equiv0\pmod q$ iff $d\equiv0\pmod p$; this gives $\mathsf{PPA}_p\subseteq\mathsf{PPA}_q$ and, choosing the branch from the bit $b$, the inclusion of the &-combination. Conversely, write $q=\prod_ip_i^{k_i}$; the designated node satisfies $\deg(v^*)\not\equiv0\pmod{p_i^{k_i}}$ for some $i$ computable locally, so the instance is a BIPARTITE$_{p_i^{k_i}}$ instance, and which prime is used depends on the instance, which is exactly what & expresses. The crux of the proof is the inclusion $\mathsf{PPA}_{p^k}\subseteq\mathsf{PPA}_p$.

## Depends on

- [The modular classes PPA_q via BIPARTITE_q and the Buss–Johnson operator & combining two classes](ppa-q-and-the-and-operator.md)

## Sources

- Mika Göös, Pritish Kamath, Katerina Sotiraki and Manolis Zampetakis, "On the Complexity of Modulo-q Arguments and the Chevalley–Warning Theorem", CCC (2020), arXiv:1912.04467.
- Alexandros Hollender, "The Classes PPA-k: Existence from Arguments Modulo k", WINE (2019), arXiv:1912.03729.
