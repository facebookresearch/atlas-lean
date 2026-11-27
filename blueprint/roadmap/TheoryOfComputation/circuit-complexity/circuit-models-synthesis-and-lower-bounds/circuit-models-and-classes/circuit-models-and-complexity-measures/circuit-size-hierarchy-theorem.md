# The circuit size hierarchy

For every sufficiently large $n$ and every integer $t$ with $1\le t\le 2^n/n$, there is a Boolean function $f$ on $n$ bits whose De Morgan circuit complexity satisfies $t< C(f)\le t+2n+3$. Consequently, if $s,s':\mathbb{N}\to\mathbb{N}$ satisfy $1\le s(n)\le s'(n)$ for every $n$, and $s'(n)\ge s(n)+2n+3$ and $s'(n)\le 2^n/n$ for all large $n$, then $\mathrm{SIZE}(s)\subsetneq\mathrm{SIZE}(s')$: more gates allow strictly more languages.

## Proof sketch

By Shannon's counting argument some function $h$ has $C(h)>2^n/n\ge t$. Change a constant function (complexity $1\le t$) into $h$ one value at a time; each step changes the complexity by at most $2n+3$ by the one-point update lemma, so the first intermediate function of complexity above $t$ has complexity in $(t,t+2n+3]$. This chain argument is Wegener's proof of his gap theorem (Theorem 10.1.1); Jukna's circuit hierarchy theorem proves the weaker separation $\mathrm{SIZE}(t)\subsetneq\mathrm{SIZE}(4t)$ for $n\le t(n)\le 2^{n-2}/n$.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Changing one value changes circuit complexity by at most 2n + 3](one-point-update-changes-complexity-by-2n-plus-3.md)
- [Shannon's sharp counting bound: almost all functions need more than 2^n/n gates](shannon-sharp-circuit-size-lower-bound.md)

## Sources

- Claude E. Shannon, "The Synthesis of Two-Terminal Switching Circuits", Bell System Technical Journal 28(1), 59–98, 1949.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987, Section 10.1.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
