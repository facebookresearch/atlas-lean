# Shannon's sharp counting bound: almost all functions need more than 2^n/n gates

There is an absolute constant $c$ such that for all sufficiently large $n$, at most $2^{2^n-(2^n/n)(\log_2 n-c)}$ of the $2^{2^n}$ Boolean functions $f:\{0,1\}^n\to\{0,1\}$ have De Morgan circuit complexity $C(f)\le 2^n/n$. Hence the fraction of $n$-variable functions with $C(f)\le 2^n/n$ tends to $0$: almost all $n$-variable functions have $C(f)>2^n/n$, so in particular $C(f)\ge(1-o(1))\,2^n/n$ for almost all $f$, and for every sufficiently large $n$ there is a function $h$ on $n$ bits with $C(h)>2^n/n$.

## Proof sketch

Count circuits up to relabelling of their gates. A circuit with $s\ge n$ gates is described by each gate's operation and its at most two arguments among the $n+s$ inputs and gates, plus the output gate: at most $(c_0(n+s))^{2s+1}$ descriptions. In a circuit of minimum size for $f$ no two gates compute the same function, so the $s!\ge(s/e)^s$ renamings of its gates give distinct descriptions of circuits for $f$. Hence at most $(c_0(n+s))^{2s+1}/s!=2^{s\log_2 s+O(s)}$ functions have $C(f)=s$, and summing over sizes up to $s=2^n/n$ adds only a factor $s+1$. With $s\log_2 s=2^n-(2^n/n)\log_2 n$ this is the stated count.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](circuit-complexity-and-formula-leaf-size.md)

## Sources

- Claude E. Shannon, "The Synthesis of Two-Terminal Switching Circuits", Bell System Technical Journal, 1949.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987.
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
