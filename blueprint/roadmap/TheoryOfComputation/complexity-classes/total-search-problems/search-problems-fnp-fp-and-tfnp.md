# Search problems: FNP, FP and TFNP

A *search problem* is a binary relation $R \subseteq \{0,1\}^* \times \{0,1\}^*$ that is polynomially balanced ($|y| \le p(|x|)$ for a polynomial $p$ whenever $(x, y) \in R$) and decidable in polynomial time; the task is, given $x$, to output some $y$ with $(x, y) \in R$ or report that none exists. $\mathsf{FNP}$ is the class of search problems, and $\mathsf{FP}$ the subclass solvable in polynomial time; $\mathsf{FP} = \mathsf{FNP}$ if and only if $\mathsf{P} = \mathsf{NP}$. A search problem is *total* if every $x$ has a solution, and $\mathsf{TFNP}$ is the class of total search problems in $\mathsf{FNP}$.

A *search reduction* from $R$ to $R'$ is a pair of polynomial-time maps $A$, sending instances of $R$ to instances of $R'$, and $B$, sending a pair $(x, y')$ to a string or to a distinguished answer $\mathsf{no}$, such that for every $x$:

1. if $A(x)$ has no $R'$-solution, then $x$ has no $R$-solution;
2. for every $y'$ with $(A(x), y') \in R'$: if $x$ has an $R$-solution then $(x, B(x, y')) \in R$, and if $x$ has none then $B(x, y') = \mathsf{no}$.

$\mathsf{FNP}$-hardness and completeness are taken with respect to these reductions. When $R'$ is total, condition 1 is vacuous and the answers $\mathsf{no}$ of $B$ certify the unsolvable instances of $R$.

## Depends on

- [Polynomial-time computable functions](../the-classes-p-np-and-conp/is-poly-time.md)
- [Polynomial-time many-one reduction](../../np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Sources

- N. Megiddo and C. H. Papadimitriou, "On total functions, existence theorems and computational complexity", *Theoretical Computer Science* 81:317–324, 1991, <http://theory.stanford.edu/~megiddo/pdf/papadimX.pdf>
- T. Roughgarden, *Stanford CS364A Algorithmic Game Theory*, Lecture 20, 2013, <https://theory.stanford.edu/~tim/f13/l/l20.pdf>
