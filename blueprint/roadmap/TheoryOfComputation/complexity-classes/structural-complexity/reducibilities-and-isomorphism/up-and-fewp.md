# Unambiguous and few-witness polynomial time: UP and FewP

$\mathsf{UP}$ is the class of languages $L$ with a polynomial-time verifier $V$ and polynomial $p$ such that for every $x$ the number of certificates $w\in\{0,1\}^{p(|x|)}$ with $V(x,w)=1$ is $1$ if $x\in L$ and $0$ otherwise. $\mathsf{FewP}$ relaxes 'exactly one' to 'at least one and at most $q(|x|)$' for a polynomial $q$. $\mathsf{P}\subseteq\mathsf{UP}\subseteq\mathsf{FewP}\subseteq\mathsf{NP}$, and both classes equal the corresponding machine classes (one accepting computation path, polynomially many accepting paths).

## Depends on

- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)

## Sources

- Leslie G. Valiant, "Relative Complexity of Checking and Evaluating", Information Processing Letters 5(1), 1976.
- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994.
