# Unambiguous space classes USPACE and UL

For $s:\mathbb{N}\to\mathbb{N}$, a language $L$ is in $\mathsf{USPACE}(s)$ if there is a nondeterministic Turing machine $M$ using $O(s(n))$ work space along every computation path, all of whose paths halt, such that for every input $x$: if $x\in L$ then $M$ has **exactly one** accepting computation path on $x$, and if $x\notin L$ it has none. $\mathsf{UL}=\mathsf{USPACE}(\log n)$. Clearly $\mathsf{UL}\subseteq\mathsf{NL}$ and $\mathsf{USPACE}(s)\subseteq\mathsf{NSPACE}(s)$.

## Depends on

- [Nondeterministic space classes](../../../time-and-space-complexity-classes/nspace.md)
- [The complexity class NL](../../../time-and-space-complexity-classes/nl.md)

## Sources

- Klaus Reinhardt and Eric Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing 29(4), 2000.
