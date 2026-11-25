# Pseudorandom generators with logarithmic seed derandomize BPP

Suppose there is a constant $c$ and a family of functions $G_m : \{0,1\}^{c \log m} \to \{0,1\}^m$, computable in time polynomial in $m$, such that for every $m$ every Boolean circuit of size at most $m$ distinguishes $G_m(U_{c \log m})$ from $U_m$ with advantage less than $1/10$. Then $\mathsf{BPP} = \mathsf{P}$: a polynomial-time machine with error at most $1/3$ is simulated deterministically by running it on $G_m(z)$ for every seed $z$ and taking the majority answer.

## Depends on

- [Pseudorandom generators against circuits](pseudorandom-generators-against-circuits.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [P is contained in P/poly](../../complexity-classes/time-and-space-complexity-classes/p-is-contained-in-p-poly.md)

## Sources

- N. Nisan and A. Wigderson, "Hardness vs randomness", *Journal of Computer and System Sciences* 49(2):149–167, 1994
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of January 2007, <https://theory.cs.princeton.edu/complexity/>, Lemma 16.4
