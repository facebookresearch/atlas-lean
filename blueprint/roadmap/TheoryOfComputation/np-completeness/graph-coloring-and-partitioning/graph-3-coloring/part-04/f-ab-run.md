# Adding the vertex counter to the OR output

For every quiescent state $m$ with counters
$n$ on stack $N$ and $r$ on stack $R$, every local state $v$ and every boolean $b$, the emitter
goes from label $\mathrm{fA}(b)$ with state $(v, m)$ to label $\mathrm{fC}(b)$, with some local
state, in exactly $2n + 2$ steps, ending in the state $m$ with the counter on $R$ replaced by
$n + r$; the counter $N$ is restored through the scratch stack $W$.
