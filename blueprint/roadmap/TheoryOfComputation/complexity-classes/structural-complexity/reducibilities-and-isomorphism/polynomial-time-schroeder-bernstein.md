# Berman–Hartmanis: polynomial-time Cantor–Schröder–Bernstein

If $A\le^{p}_{m}B$ and $B\le^{p}_{m}A$ via one-one, length-increasing reductions $f,g$ with polynomial-time left inverses, then $A$ and $B$ are p-isomorphic; the isomorphism $h$ satisfies $h(x)=f(x)$ or $g(h(x))=x$ for every $x$. Consequently, any two paddable languages that are many-one interreducible are p-isomorphic; in particular two paddable $\mathsf{NP}$-complete sets are p-isomorphic, and SAT is paddable.

## Proof sketch

For $x$, follow the chain of preimages $x, g^{-1}(x), f^{-1}(g^{-1}(x)),\dots$; length-increase makes the chain polynomially short, and the parity of where it stops decides whether $h(x)=f(x)$ or $h(x)=g^{-1}(x)$, as in the classical proof. Padding upgrades any reduction into a paddable target to a one-one length-increasing invertible one.

## Depends on

- [Paddable languages and polynomial-time isomorphism](paddable-languages-and-p-isomorphism.md)

## Sources

- Leonard Berman and Juris Hartmanis, "On Isomorphisms and Density of NP and Other Complete Sets", SIAM Journal on Computing 6(2), 1977.
