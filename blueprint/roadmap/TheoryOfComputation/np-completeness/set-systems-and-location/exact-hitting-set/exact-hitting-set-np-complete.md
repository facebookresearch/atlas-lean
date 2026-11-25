# Karp's HITTING SET is NP-complete

The exact hitting set decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Karp proves it by reducing EXACT COVER: given sets $S_j$ over elements $u_i$, take one element $s_j$ per set and one subset $U_i = \{s_j : u_i \in S_j\}$ per element; a subfamily of the $S_j$ is an exact cover exactly when the corresponding set $W$ of $s_j$ meets every $U_i$ once. With the number of elements written in binary, this would list exponentially many subsets $U_i$ when most elements lie in no set; but an element in no set makes the EXACT COVER instance a no-instance, so the reduction first checks that every element lies in some listed set (which bounds the number of elements by the total length of the lists) and otherwise outputs a fixed no-instance, as it does for inputs that are not well-formed instances.

## Informally uses

- [EXACT COVER is NP-complete](../exact-cover/exact-cover-np-complete.md): the source problem of Karp's reduction.

## Sources

- Richard M. Karp, "Reducibility among combinatorial problems", in Raymond E. Miller and James W. Thatcher (eds.), *Complexity of Computer Computations*, Plenum Press, 1972, 85–103, the reduction EXACT COVER ∝ HITTING SET. Reprinted in Michael Jünger et al. (eds.), *50 Years of Integer Programming 1958–2008*, Springer, 2010, chapter 8, 219–241.
