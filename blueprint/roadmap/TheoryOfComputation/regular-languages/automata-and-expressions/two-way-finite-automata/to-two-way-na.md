# A deterministic two-way automaton as a nondeterministic one

A deterministic two-way
automaton $A$ is viewed as the nondeterministic two-way automaton with the same states and
accepting states, whose only start state is the start state of $A$, and which can go from state
$q$ reading a symbol $a$ to state $q'$ with head move $m$ exactly when the step function of $A$
at $q$ and $a$ returns $q'$ and $m$.
