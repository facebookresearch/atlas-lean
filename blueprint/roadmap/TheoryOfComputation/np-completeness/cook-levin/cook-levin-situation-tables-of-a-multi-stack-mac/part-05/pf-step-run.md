# Pushed-fill forcing on a real run

Let $E$ be an encoding of the machine $M$ with $K$
stacks and layout $L$, let $d$ be the window depth of $M$, let $H \in \mathbb{N}$ with $d \le H$,
let $W$ be the row width of $L$ at height $H$, and write $X[t, x] = tW + x$ for the label/state
variables and $C[t, k, j, x]$ for the cell variable of row $t$, stack $k$, depth $j$ and symbol
code $x$. Fix an input list $s$, let $c_n$ be the configuration after $n$ steps of the
idle-extended run of $M$ from the initial configuration on $s$, let $T, t \in \mathbb{N}$ with
$t < T$, let $i$ be the situation index of $c_t$, and suppose every stack of $c_t$ has length at
most $H - d$. Let the assignment $a$ satisfy the cell-shift family of $E$ (tables $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ and $N$ situations) for $T$ and $H$, and suppose
$X[t + 1, \mathrm{sa}(i)]$ is true under $a$. Then for all $k < K$ and $j < \mathrm{pl}(i, k)$ the
variable $C[t + 1, k, j, x]$ is true under $a$, where $x$ is the code of the cell of $c_{t+1}$ at
stack $k$ and depth $j$ (code $0$ if that cell is empty).
