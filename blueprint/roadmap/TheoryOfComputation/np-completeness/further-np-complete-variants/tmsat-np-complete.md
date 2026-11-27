# TMSAT is NP-complete

$\mathrm{TMSAT}=\{\langle\alpha,x,1^{n},1^{t}\rangle : \exists u\in\{0,1\}^{n}$ such that the machine described by $\alpha$, run on input $x$ and certificate $u$, outputs $1$ within $t$ steps$\}$ is $\mathsf{NP}$-complete under polynomial-time many-one reductions.

## Proof sketch

Membership: guess $u$ and run the clocked universal machine for $t$ steps, which takes time polynomial in $|\alpha|+|x|+t$. Hardness: for $L\in\mathsf{NP}$ with verifier $M$ running in time $p$ on certificates of length $q$, map $x\mapsto\langle\llcorner M\lrcorner,x,1^{q(|x|)},1^{p(|x|)}\rangle$.

## Depends on

- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [The clocked universal function is polynomial-time computable](../../turing-machines/universal-machines/clocked-universal-turing-machine/nonempty-univ-poly-time.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Theorem 2.9 (published by Cambridge University Press, 2009).
