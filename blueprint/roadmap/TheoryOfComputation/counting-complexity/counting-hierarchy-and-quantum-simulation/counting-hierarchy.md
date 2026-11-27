# The counting hierarchy CH

The **counting hierarchy** is defined by $\mathsf{C}_0\mathsf{P}=\mathsf{P}$ and $\mathsf{C}_{k+1}\mathsf{P}=\mathsf{PP}^{\mathsf{C}_k\mathsf{P}}$ (equivalently, strict-majority polynomial-time verifiers relative to a $\mathsf{C}_k\mathsf{P}$ oracle), with $\mathsf{CH}=\bigcup_k\mathsf{C}_k\mathsf{P}$. By Toda's theorem $\mathsf{PH}\subseteq\mathsf{C}_2\mathsf{P}$ (indeed $\subseteq\mathsf{P}^{\mathsf{PP}}$), and $\mathsf{CH}\subseteq\mathsf{PSPACE}$.

## Depends on

- [Probabilistic polynomial time with unbounded error](../../complexity-classes/time-and-space-complexity-classes/pp.md)
- [Polynomial space for decision problems](../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Sources

- Klaus W. Wagner, "The Complexity of Combinatorial Problems with Succinct Input Representation", Acta Informatica 23(3), 1986.
- Seinosuke Toda, "PP Is as Hard as the Polynomial-Time Hierarchy", SIAM Journal on Computing 20(5), 1991.
