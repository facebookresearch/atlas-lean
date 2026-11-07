# Step count of the Horner rounds

For a list $cs$ of coefficients, a base $b$ and an
accumulator value $A$: $0$ if $cs$ is empty, and if $cs$ is $a$ followed by $cs'$, the step count
$h(A, b)$ of one Horner round from $A$ with base $b$ plus the step count of $cs'$ with base $b$
from accumulator $A b + a$. This is the exact number of steps of the Horner rounds.
