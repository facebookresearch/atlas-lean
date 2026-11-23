# Feasible exact-hitting-set instances

An exact-hitting-set instance $(r, U)$ is feasible when there is a finite set $W$ of elements less than $r$ such that every listed subset $U_i$ contains exactly one element of $W$, that is $|W \cap U_i| = 1$ for each $i$ (counted with multiplicity in the list, which for well-formed instances is the size of the intersection).

This is Karp's HITTING SET. It is not the hitting set problem of Garey and Johnson, which asks for at most $K$ elements meeting every $U_i$ at least once.

## Sources

- Richard M. Karp, "Reducibility among combinatorial problems", in Raymond E. Miller and James W. Thatcher (eds.), *Complexity of Computer Computations*, Plenum Press, 1972, 85–103, the reduction EXACT COVER ∝ HITTING SET. Reprinted in Michael Jünger et al. (eds.), *50 Years of Integer Programming 1958–2008*, Springer, 2010, chapter 8, 219–241.
