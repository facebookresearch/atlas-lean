# Book: polynomial-power space classes are not closed under polynomial-time reductions

For every $k\ge 1$, $\mathsf{DSPACE}(n^k)$ is different from every class that is closed under polynomial-time many-one reductions. In particular

$$
\mathsf{DSPACE}(n)\ne\mathsf{NP},\qquad \mathsf{DSPACE}(n)\ne\mathsf{P},\qquad \mathsf{DSPACE}(n)\ne\mathsf{PSPACE}.
$$

## Proof sketch

By the space hierarchy theorem there is $L\in\mathsf{DSPACE}(n^{k+1})\setminus\mathsf{DSPACE}(n^k)$. The padded language $L'=\{x\#1^{|x|^{k+1}-|x|}\}$ lies in $\mathsf{DSPACE}(n)\subseteq\mathsf{DSPACE}(n^k)$ and $L$ reduces to $L'$ in polynomial time, so $\mathsf{DSPACE}(n^k)$ is not closed under such reductions, unlike $\mathsf{NP}$, $\mathsf{P}$ and $\mathsf{PSPACE}$.

## Depends on

- [Deterministic space classes on multi-tape machines](../../../time-and-space-classes-on-multi-tape-machines/dspace.md)
- [The complexity class NP](../../../the-classes-p-np-and-conp/np.md)
- [The complexity class P](../../../the-classes-p-np-and-conp/p.md)
- [Polynomial space for decision problems](../../../time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Space hierarchy theorem for space-constructible bounds](../../../../hierarchy-theorems-and-barriers/space-hierarchy-theorem/space-hierarchy-theorem-for-space-constructible.md)

## Sources

- Ronald V. Book, "Comparing Complexity Classes", Journal of Computer and System Sciences 9(2), 1974.
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007, Chapter 3, Exercise 2.
