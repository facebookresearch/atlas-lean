# The circuit size hierarchy

For every sufficiently large $n$ and every integer $t$ with $1\le t\le 2^n/n$, there is a Boolean function $f$ on $n$ bits whose De Morgan circuit complexity satisfies $t< C(f)\le t+2n+3$. Consequently, if $s,s':\mathbb{N}\to\mathbb{N}$ satisfy $s'(n)\ge s(n)+2n+3$ and $s'(n)\le 2^n/n$ for all large $n$, then $\mathrm{SIZE}(s)\subsetneq\mathrm{SIZE}(s')$: more gates allow strictly more languages.

## Proof sketch

By Shannon's counting argument some function $h$ has $C(h)>2^n/n$. Change a constant function into $h$ one value at a time; each step changes the complexity by at most $2n+3$ by the one-point update lemma, so by discrete continuity some intermediate function has complexity in $(t,t+2n+3]$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Changing one value changes circuit complexity by at most 2n + 3](one-point-update-changes-complexity-by-2n-plus-3.md)
- [Shannon's sharp counting bound: almost all functions need more than 2^n/n gates](shannon-sharp-circuit-size-lower-bound.md)

## Sources

- Claude E. Shannon, "The Synthesis of Two-Terminal Switching Circuits", Bell System Technical Journal, 1949.
- Sanjeev Arora, Boaz Barak, "Computational Complexity: A Modern Approach", Draft of a book, web draft dated 2007-01-08, 2007.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
