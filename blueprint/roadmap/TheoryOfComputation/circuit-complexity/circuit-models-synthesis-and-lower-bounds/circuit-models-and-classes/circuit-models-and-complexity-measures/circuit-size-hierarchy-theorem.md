# The circuit size hierarchy

Let $C$ denote De Morgan circuit complexity (basis $\{\wedge,\vee,\neg\}$, every gate charged). A Boolean function $f$ on $n$ bits *depends essentially* on all $n$ variables if for every $i$ some two inputs differing only in the $i$-th bit get different values; let $C(B^*_n)$ be the largest complexity of such a function. There is an absolute constant $k$ such that for every $n$ and every integer $t$ with $n-2\le t<C(B^*_n)$ there is a function $f$ on $n$ bits depending essentially on all $n$ variables with

$$t< C(f)\le t+kn.$$

Thus the circuit size hierarchy for $n$-variable functions has no gaps longer than $kn$.

## Proof sketch

Wegener's chain argument: take a function $h$ depending essentially on all $n$ variables of maximal complexity, list $h^{-1}(1)=\{a_1,\dots,a_r\}$, and build the chain $f_0\equiv0$, $f_j=f_{j-1}\vee m_{a_j}$, where $m_a$ is the minterm of $a$. Each step raises the complexity by at most a constant times $n$ (a minterm costs $O(n)$ De Morgan gates, plus one disjunction), and functions in the chain that do not depend on all variables are repaired by a disjunction with a monomial in the missing variables, at the same cost; so the first function of the chain with complexity above $t$ has complexity at most $t+kn$. Wegener proves the explicit increments $1$ and $n$ for the bases $B_2$, $U_2$ and the monotone basis, and an increment $k(\Omega)n$ for every complete basis $\Omega$ "by the same methods". (Derived, not stated by the sources: with a De Morgan minterm of at most $2n-1$ gates the increment is at most $2n$ per step, and with Shannon's counting bound, which gives functions with $C(h)>2^n/n$ for large $n$, one gets for every sufficiently large $n$ and $1\le t\le 2^n/n$ a function with $t< C(f)\le t+2n+3$; consequently, if $s,s':\mathbb{N}\to\mathbb{N}$ satisfy $1\le s(n)\le s'(n)$, $s'(n)\ge s(n)+2n+3$ and $s'(n)\le 2^n/n$ for all large $n$, then $\mathrm{SIZE}(s)\subsetneq\mathrm{SIZE}(s')$. Jukna's circuit hierarchy theorem proves the weaker separation $\mathrm{SIZE}(t)\subsetneq\mathrm{SIZE}(4t)$ for $n\le t(n)\le 2^{n-2}/n$.)

## Depends on

- [Circuit complexity, binary cost and formula leaf size](circuit-complexity-and-formula-leaf-size.md)

## Proof depends on

- [Shannon's sharp counting bound: almost all functions need more than 2^n/n gates](shannon-sharp-circuit-size-lower-bound.md)

## Sources

- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987, Section 10.1: Theorem 1.1, equations (1.6)–(1.7) for a complete basis $\Omega \subseteq B_2$, and its proof (equations (1.8)–(1.15)).
- Claude E. Shannon, "The Synthesis of Two-Terminal Switching Circuits", Bell System Technical Journal 28(1), 59–98, 1949.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
