# Explicit steps agree with the decoded machine

For every code $c$ and every configuration
$k$ of the simulation, the decoded TM0 machine of $c$ halts at the TM0 configuration of $k$
exactly when the step of $c$ from $k$ is undefined, and otherwise its step from the TM0
configuration of $k$ is the TM0 configuration of the step of $c$ from $k$.
