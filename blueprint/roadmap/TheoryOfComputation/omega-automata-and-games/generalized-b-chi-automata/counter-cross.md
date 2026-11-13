# The degeneralization counter crosses every value below its target

Let $g$ be a
generalized Büchi automaton with acceptance sets $F_0, \dots, F_{k-1}$ and counter update
$\mathrm{next}$, let $s$ be an infinite sequence of states, and let $c_0, c_1, \dots$ be any
sequence in $\{0, \dots, k\}$ with $c_{n+1} = \mathrm{next}(c_n, s_{n+1})$ for every $n$. Let
$a \le b$ be times with $c_a = 0$ and $c_b = d \le k$, and suppose $c_t \ne k$ for every $t$ with
$a < t < b$. Then for every $j < d$ there is a time $t$ with $a \le t < b$ such that $c_t = j$,
$c_{t+1} = j + 1$ and $s_{t+1} \in F_j$.

The proof is by induction on $b$, case-splitting the last counter step into stay, advance, or
the impossible reset.
