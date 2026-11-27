# Positive shift step on a real run (L3⁺)

Let $M$ be a finite multi-stack Turing machine
and $E$ an encoding of $M$ with $K$ numbered stacks, tables $sa$, $pl$, $cn$, $pu$ and $N$
situations, let $T, H, t \in \mathbb{N}$ with $t < T$, and let $a$ be an assignment satisfying
the cell-shift clause family of the layout of $E$ with these tables and bounds $N$, $T$, $H$.
Call a variable true when its index is less than the length of $a$ and $a$ is true there. Write
$S[t, i]$ for the label/state variable $sa(i)$ of row $t + 1$, $C[t, k, j, x]$ for the cell
variable of row $t$, stack $k$, depth $j$ and symbol code $x$ (both at height $H$), and
$\mathrm{cell}(c, k, j)$ for the code at depth $j$ of the stack numbered $k$ of a configuration
$c$ ($0$ if there is none). Fix an input list $s$, let $c_n$ be the configuration after $n$
idle-extended steps of $M$ from the initial configuration on $s$, and let $i$ be the situation
index of $c_t$. Suppose that every stack of $c_t$ has length at most $H - d$, where $d$ is the
window depth of $M$, that $C[t, k', j', \mathrm{cell}(c_t, k', j')]$ is true for all $k' < K$
and $j' < H$, and that $S[t, i]$ is true. Then for every $k < K$ and every $j$ with
$pl(i, k) \le j < H - \max(pl(i, k), cn(i, k)) + pl(i, k)$, the variable
$C[t + 1, k, j, \mathrm{cell}(c_{t+1}, k, j)]$ is true. Subtraction is truncated at $0$.
