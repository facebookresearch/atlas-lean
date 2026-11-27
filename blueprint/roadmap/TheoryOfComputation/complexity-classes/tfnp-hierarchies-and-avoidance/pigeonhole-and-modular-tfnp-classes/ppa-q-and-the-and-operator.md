# The modular classes PPA_q via BIPARTITE_q and the Buss–Johnson operator & combining two classes

Fix an integer $q\ge2$. **BIPARTITE$_q$**: a balanced bipartite graph $G=(V\cup U,E)$ with $V\cup U=\{0,1\}^n$ is given by a circuit computing the neighbourhood of each node, together with a designated node $v^*$. A solution is $v^*$ if $\deg(v^*)\equiv0\pmod q$ (trivial solution), or any $v\ne v^*$ with $\deg(v)\not\equiv0\pmod q$. It embodies the principle: if a bipartite graph has a node whose degree is not a multiple of $q$, it has another one. $\mathsf{PPA}_q$ (also written PPA-$q$) is the class of total search problems many-one reducible to BIPARTITE$_q$; the variants LONELY$_q$ and LEAF$_q$ define the same class, and $\mathsf{PPA}_2=\mathsf{PPA}$.

**The operator &.** For syntactic classes $\mathsf M_0,\mathsf M_1$ with complete problems $S_0,S_1$, the class $\mathsf M_0\,\&\,\mathsf M_1$ is defined by the complete problem $S_0\,\&\,S_1$: on input $(x,b)\in\{0,1\}^*\times\{0,1\}$, output a solution of $x$ viewed as an instance of $S_b$. Then $\mathsf M_0\cup\mathsf M_1\subseteq\mathsf M_0\,\&\,\mathsf M_1$, and $\&_{i}\mathsf M_i$ is defined likewise for finitely many classes.

## Depends on

- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- Mika Göös, Pritish Kamath, Katerina Sotiraki and Manolis Zampetakis, "On the Complexity of Modulo-q Arguments and the Chevalley–Warning Theorem", CCC (2020), arXiv:1912.04467.
- Alexandros Hollender, "The Classes PPA-k: Existence from Arguments Modulo k", WINE (2019), arXiv:1912.03729.
- Samuel R. Buss and Alan S. Johnson, "Propositional Proofs and Reductions between NP Search Problems", Annals of Pure and Applied Logic 163(9) (2012).
