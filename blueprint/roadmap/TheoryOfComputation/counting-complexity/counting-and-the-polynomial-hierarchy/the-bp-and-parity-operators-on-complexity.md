# The BP and parity operators on complexity classes

Let $\mathcal{C}$ be a class of languages. A language $L$ is in $\mathsf{BP}\cdot\mathcal{C}$ if there are a language $A \in \mathcal{C}$ and a polynomial $p$ such that for every $x$, $\Pr_{r \in \{0,1\}^{p(|x|)}}[\langle x, r\rangle \in A \iff x \in L] \ge 2/3$. A language $L$ is in $\oplus\cdot\mathcal{C}$ if there are $A \in \mathcal{C}$ and a polynomial $p$ such that $x \in L$ exactly when the number of $w \in \{0,1\}^{p(|x|)}$ with $\langle x, w\rangle \in A$ is odd; $\oplus\mathsf{P} = \oplus\cdot\mathsf{P}$.

## Depends on

- [The counting class $\#P$](../../complexity-classes/time-and-space-complexity-classes/sharp-p.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Sources

- S. Toda, "PP is as hard as the polynomial-time hierarchy", *SIAM Journal on Computing* 20(5):865–877, 1991
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009
