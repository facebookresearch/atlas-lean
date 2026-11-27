# Transition families with a run-literal head are satisfied by the run

Let $E$ be an
encoding of the machine $M$ with layout $L$, $N$ situations, label/state table $\mathrm{la}$ and
window table $\mathrm{wa}$, let $d$ be the window depth of $M$, and let $T, H \in \mathbb{N}$ with
$d \le H$. Write $X[r, x]$ for the index of the label/state variable $x$ of row $r$ at height
$H$. Fix an input list $s$, let $c_t$ be the configuration after $t$ steps of the idle-extended
run of $M$ from the initial configuration on $s$, and let $\nu : \mathbb{N} \to \mathbb{N}$ be a
next-label table such that $\mathrm{la}$, $\nu$ and $\mathrm{wa}$ are well formed for $L$ at
height $H$ for every situation $i < N$. Suppose that for every $t < T$, with $i_t$ the situation
index of $c_t$, the index $X[t + 1, \nu(i_t)]$ is one of the real run's literals of $s$ at
height $H$. Then the assignment of the real run's literals of $s$ for $T$ and $H$ satisfies the
transition clause family of $L$ with the tables $\mathrm{la}$, $\nu$ and $\mathrm{wa}$ for $T$,
$H$ and $N$.

In clause $(t, i)$ the head literal is true when $i$ is the situation index of $c_t$; otherwise
the clause is satisfied by a body literal whose variable is false, by situation injectivity.
