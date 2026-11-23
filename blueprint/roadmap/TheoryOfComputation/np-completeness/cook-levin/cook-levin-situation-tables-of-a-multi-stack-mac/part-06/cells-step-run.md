# Cell literals propagate one step along the real run

Let $E$ be an encoding of a machine
$M$ with window depth $d$, let $s$ be a list of symbols of the input stack of $M$, and for each
$n$ let $c_n$ be the configuration after $n$ steps of the idle-extended run of $M$ from its
initial configuration on $s$. Let $T, H, t$ be natural numbers with $t < T$ and $d \le H$.
Suppose an assignment $a$ satisfies the transition clause family of $E$ with the
situation-variable table $\mathrm{sa}$ in place of the next-label table (the S-definition family)
at $T$, $H$ and the number $N$ of situations of $E$, and satisfies the cell-shift clause family
of $E$ at $N$, $T$, $H$. Suppose also that every stack of $c_t$ has length at most $H - d$, that
the code literal of $c_t$ holds in row $t$ (the label/state variable of row $t$ for the code of
$c_t$ is true under $a$), and that the cell literals of $c_t$ hold in row $t$ (for every stack
number $k$ below the number of stacks and every depth $j < H$, the cell variable of row $t$ for
stack $k$, depth $j$ and the code of the symbol of $c_t$ there, $0$ if there is none, is true
under $a$). Then the cell literals of $c_{t+1}$ hold in row $t + 1$.
