# Runs of a machine given by a transition function

Let $\delta$ be a transition function
that assigns an action to every state, symbol or blank read on the input tape, and tuple of
symbols or blanks read on the work tapes, and let $M$ be the deterministic multi-tape Turing
machine with initial state $q_0$ and transition function $\delta$. Let $S_\delta$ be the map on
configurations that fixes every halted configuration and sends a running configuration in state
$q$ to the result of applying to it the action that $\delta$ selects for $q$ and the symbols or
blanks under its heads. For every configuration $c$ and every $t \in \mathbb{N}$, the run of $M$
from $c$ is in configuration $S_\delta^t(c)$ after $t$ steps, where $S_\delta^t$ is the $t$-fold
iterate of $S_\delta$.
