# Encoding data for a finite TM2 machine

An encoding of a finite TM2 machine $M$ consists
of a number $K$, a map $\kappa$ from the stacks of $M$ to the naturals below $K$ and a map
$\kappa'$ from naturals to stacks with $\kappa'(\kappa(k)) = k$ for every stack $k$ and
$\kappa(\kappa'(n)) = n$ for every $n < K$; a number $A_0$, a map $\lambda$ from pairs (label
or halted, state) to the naturals below $A_0$ and a map $\lambda'$ back with
$\lambda'(\lambda(x)) = x$ for every pair $x$ and $\lambda(\lambda'(a)) = a$ for every
$a < A_0$; and for each stack $k$ a size $s_k$, effective symbols $d_k(i)$ for $i < s_k$, and a
symbol code map $e_k$ on the alphabet of stack $k$ with $e_k(d_k(i)) = i + 1$. It is required
that every symbol that a push node of the statement tree of some label can push onto stack $k$,
for some state, is an effective symbol of stack $k$, and that every symbol of the input stack's
alphabet is an effective symbol of the input stack.

Symbol code $0$ stands for $\bot$, the empty cell.
