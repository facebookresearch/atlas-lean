# Jeřábek: integer factoring randomly reduces to PPA and to WEAK-PIGEON, and modular square roots lie in PPA

Recall COLLISION (PPP-complete): given a circuit $C:\{0,1\}^n\to\{0,1\}^n$ find $x$ with $C(x)=0^n$ or $x\ne y$ with $C(x)=C(y)$. WEAK-PIGEON gives $C:\{0,1\}^n\to\{0,1\}^{n-1}$ and asks for a collision; PWPP is the class reducible to it ($\mathsf{PWPP}\subseteq\mathsf{PPP}$). FACROOT: given integers $n$ and $a$ with Jacobi symbol $(a|n)=1$, find a proper divisor of $n$ or a square root of $a$ modulo $n$. Then:

1. FACROOT $\in\mathsf{PPA}$;
2. integer factoring is reducible in randomized polynomial time to FACROOT, hence to a PPA problem, and also to WEAK-PIGEON;
3. under the generalized Riemann hypothesis both reductions are deterministic, so factoring lies in $\mathsf{PPA}\cap\mathsf{PPP}$ and is polynomial-time reducible to WEAK-PIGEON;
4. unconditionally, PPA contains the problems: given $n,a$, find a square root of $a$ modulo $n$ or a witness that $a$ is a quadratic nonresidue; given odd non-square $n$, find $a$ with $(a|n)=-1$.

## Proof sketch

The totality of FACROOT is provable in the bounded-arithmetic theory $S^1_2+\mathrm{Count}_2(\mathrm{PV})$, which proves quadratic reciprocity and the soundness of the Jacobi-symbol algorithm, and a witnessing theorem converts this into PPA membership; the paper gives a direct parity-graph proof. Factoring reduces to FACROOT by choosing random $a$ with $(a|n)=1$ and using that a square root of $a^2$ different from $\pm a$ reveals a factor. A similar probabilistic argument yields the reduction to WEAK-PIGEON; under GRH the random choices can be replaced by small explicit ones.

## Depends on

- [The modular classes PPA_q via BIPARTITE_q and the Buss–Johnson operator & combining two classes](ppa-q-and-the-and-operator.md)
- [Search problems: FNP, FP and TFNP](../../total-search-problems/search-problems-fnp-fp-and-tfnp.md)

## Sources

- Emil Jeřábek, "Integer Factoring and Modular Square Roots", Journal of Computer and System Sciences (2016), arXiv:1207.5220.
- Mika Göös, Pritish Kamath, Katerina Sotiraki and Manolis Zampetakis, "On the Complexity of Modulo-q Arguments and the Chevalley–Warning Theorem", CCC (2020), arXiv:1912.04467.
