# Bounded execution only reaches codes of reachable states

Let $p$ be a URM program,
$x$ an input and $t$ a natural number. Then there is a machine state $s'$, reachable from the
initial state with input list $[x]$ by steps of $p$, whose coded state equals the result of
bounded execution for $t$ steps on the instruction codes of $p$ from the initial coded state
for $x$.
