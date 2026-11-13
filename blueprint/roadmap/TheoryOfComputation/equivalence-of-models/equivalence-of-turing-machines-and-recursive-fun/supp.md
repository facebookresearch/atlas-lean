# Support of a code

For a code $c$, the support of $c$ is the finite set of labels of
Mathlib's code evaluator $\mathrm{tr}$ that Mathlib associates with evaluating $c$ under the
halting continuation.

It contains the label at which this evaluation starts and is closed under the steps of
$\mathrm{tr}$, so it contains every label reachable from there.
