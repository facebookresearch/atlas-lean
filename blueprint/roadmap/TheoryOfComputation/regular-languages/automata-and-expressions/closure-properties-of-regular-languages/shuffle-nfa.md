# Shuffle automaton of two DFAs

Let $M$ and $N$ be DFAs over $\alpha$ with state types
$\sigma$ and $\tau$, start states $s_M$ and $s_N$, sets of accepting states $F_M$ and $F_N$, and
transition functions $\delta_M$ and $\delta_N$. Their shuffle automaton is the NFA over $\alpha$
with state type $\sigma \times \tau$, the single start state $(s_M, s_N)$ and accepting states
$F_M \times F_N$, which on a letter $a$ moves from a state $(p, q)$ to the two states
$(\delta_M(p, a), q)$ and $(p, \delta_N(q, a))$.
