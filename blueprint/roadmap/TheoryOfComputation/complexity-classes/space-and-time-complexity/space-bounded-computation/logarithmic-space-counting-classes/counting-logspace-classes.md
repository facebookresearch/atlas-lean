# The counting classes #L and Mod_k L

$\#\mathsf{L}$ is the class of functions $f:\{0,1\}^*\to\mathbb{N}$ for which there is a nondeterministic logarithmic-space machine $M$, all of whose branches halt in polynomial time, with $f(x)$ equal to the number of accepting computation paths of $M$ on $x$. For a fixed modulus $k\ge 2$, $\mathsf{Mod}_k\mathsf{L}$ is the class of languages $\{x: f(x)\not\equiv 0 \pmod k\}$ for $f\in\#\mathsf{L}$; $\oplus\mathsf{L}=\mathsf{Mod}_2\mathsf{L}$ is the class of languages decided by odd numbers of accepting paths. Since an unambiguous count is $0$ or $1$, $\mathsf{UL}\subseteq\mathsf{Mod}_k\mathsf{L}$ for every $k\ge 2$.

## Depends on

- [Unambiguous space classes USPACE and UL](unambiguous-space-classes.md)
- [The complexity class NL](../../../time-and-space-complexity-classes/nl.md)

## Sources

- Klaus Reinhardt and Eric Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing 29(4), 2000.
