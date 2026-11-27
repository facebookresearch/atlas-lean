# Fooling sets give single-tape time lower bounds; palindromes need quadratic time

Suppose that on inputs of the form $\ell(x)\,m\,r(y)$ with a common middle word $m$ of length $L$ a language computes $f(x,y)$. If $f$ has a fooling set $S$ (pairs $(x,y)$ with $f(x,y)=b$ such that for distinct pairs $(x,y),(x',y')\in S$ one of $f(x,y'),f(x',y)$ differs from $b$), then every single-tape decider has, at each boundary in the middle word, crossing sequences distinguishing all of $S$, so it runs in time $\Omega(L\cdot\log|S|/\log|Q|)$ on some input. Consequently single-tape machines need time $\Omega(n^{2})$ to decide palindromes $\{ww^{R}\}$, the copy language $\{w\#w\}$ (or $\{ww\}$) and binary inner product.

## Proof sketch

Equal crossing sequences for two pairs at a boundary in the middle would, by cut and paste, let the machine accept a mixed input contradicting the fooling property; there are at most $|Q|^{\ell}$ sequences of length $\ell$, so some sequence has length $\ge\log|S|/\log|Q|$, at every one of the $L$ boundaries. For palindromes take $S$ the identity pairs $(x,x)$ of length $n/3$ with a middle block of zeros.

## Depends on

- [Crossing sequences of single-tape Turing machines](crossing-sequences.md)

## Sources

- F. C. Hennie, "One-tape, off-line Turing machine computations", Information and Control 8(6), 553–578, 1965.
- Eyal Kushilevitz and Noam Nisan, "Communication Complexity", Cambridge University Press, 1997, Chapter 12 (Turing-machine time lower bounds from communication complexity).
