# Transition clauses force the next label

Let $L$ be a layout with $K$ stacks and window
depth $d$, let $\mathrm{la}, \mathrm{na} : \mathbb{N} \to \mathbb{N}$ and
$\mathrm{wa} : \mathbb{N} \to \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ be tables, and let $a$ be
an assignment satisfying the transition clause family of $L$, $\mathrm{la}$, $\mathrm{na}$ and
$\mathrm{wa}$ for bounds $T$, $H$ and $N$. Write $X[t, b]$ and $C[t, k, j, x]$ for the
label/state and cell variables at height $H$. Suppose $t < T$, $i < N$, $X[t, \mathrm{la}(i)]$ is
true under $a$, and for every $n < Kd$, writing $q = \lfloor n / d \rfloor$ and
$r = n \bmod d$, the variable $C[t, q, r, \mathrm{wa}(i, q, r)]$ is true under $a$. Then
$X[t + 1, \mathrm{na}(i)]$ is true under $a$.

The window literals are indexed by $n$ exactly as in the clause, and no one-hot hypothesis on $a$
is needed.
