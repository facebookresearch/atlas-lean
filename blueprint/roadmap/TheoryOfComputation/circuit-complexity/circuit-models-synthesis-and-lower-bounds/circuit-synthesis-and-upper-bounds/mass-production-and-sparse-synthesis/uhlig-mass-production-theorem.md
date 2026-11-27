# Uhlig's mass-production theorem

Let $d:\mathbb{N}\to\mathbb{N}$ satisfy $d(n)\log_2 n=o(n)$. Then every Boolean function $f$ on $n$ inputs satisfies

$$
C\bigl(f^{\times 2^{d(n)}}\bigr)\le(1+o(1))\,\frac{2^n}{n},
$$

uniformly in $f$: up to $2^{d(n)}$ independent copies of any $n$-variable function cost no more, asymptotically, than the worst-case single-copy bound of Lupanov.

## Proof sketch

The two-copy step (Wegener's proof for $r=2$) evaluates $f$ on two inputs $(i,x')$ and $(j,y')$ with $p$-bit prefixes $i,j$ from the $2^p+1$ prefix differences $g_0=f_0$, $g_l=f_{l-1}\oplus f_l$, $g_{2^p}=f_{2^p-1}$ of the subfunctions $f_l$ on the remaining $m$ inputs, each evaluated once on a selected argument, since $f_i=g_0\oplus\cdots\oplus g_i$ and $f_j=g_{j+1}\oplus\cdots\oplus g_{2^p}$ when $i\le j$; applying the step to each of these functions in turn, iterating $d$ layers with $p=2\log_2 n+2$ multiplies the size by $(2^p+1)^d$ and adds lower-order overhead, which Lupanov's bound absorbs when $d\log n=o(n)$.

## Depends on

- [Mass complexity of a Boolean function](mass-complexity-of-a-boolean-function.md)

## Proof depends on

- [Lupanov's asymptotic circuit upper bound](../circuit-synthesis-upper-bounds/lupanov-circuit-upper-bound.md)

## Sources

- Dietmar Uhlig, "Networks Computing Boolean Functions for Multiple Input Values", in M. S. Paterson (ed.), Boolean Function Complexity, London Mathematical Society Lecture Note Series 169, Cambridge University Press, 1992.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987, Theorem 10.2.3.
