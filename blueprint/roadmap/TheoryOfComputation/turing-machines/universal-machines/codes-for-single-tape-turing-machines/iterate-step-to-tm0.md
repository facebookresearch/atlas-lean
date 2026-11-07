# Iterated steps of the decoded machine

Let $c$ be a code, $n \in \mathbb{N}$ and $k$
an explicit configuration. Run the machine of $c$ for $n$ steps from the Mathlib configuration
of $k$, and run the explicit simulation of $c$ for $n$ steps from $k$, where a run that reaches
a configuration without a successor before completing $n$ steps has no result. Then the first
run has a result exactly when the second does, and its result is the Mathlib configuration of
the result of the second.
