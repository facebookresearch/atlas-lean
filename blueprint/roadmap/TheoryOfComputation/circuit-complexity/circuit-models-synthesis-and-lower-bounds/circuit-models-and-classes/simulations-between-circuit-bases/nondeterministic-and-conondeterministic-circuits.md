# Nondeterministic and conondeterministic circuits

Let $C$ be a Boolean circuit on $n+p$ inputs, read as $C(x,r)$ with $x\in\{0,1\}^n$ and a *witness* (or guess) $r\in\{0,1\}^p$. The *nondeterministic* circuit $C$ computes $x\mapsto\exists r\,C(x,r)$, and the *conondeterministic* circuit computes $x\mapsto\forall r\,C(x,r)$. A set $S\subseteq\{0,1\}^n$ is decided nondeterministically by $C$ if $x\in S\iff\exists r\, C(x,r)=1$; the number $p$ of witness inputs is arbitrary.

## Depends on

- [Straight-line programs and circuits over a basis](../circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)
- [The complexity class NP](../../../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
