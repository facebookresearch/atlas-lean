# Computed earliest change of a gate with no inputs

For a gate with no inputs, the computed earliest change time is $\infty$: the minimum over its empty fan-in is $\infty$, and the contamination delay is added to it. This is a statement about the computed bound. For a causal gate output it means that the output is constant on $[0, \infty)$; times before $0$ are unconstrained, so even a causal gate with no inputs may have changed at time $-1$.
