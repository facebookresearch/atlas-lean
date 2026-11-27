# Earliest change of a gate

For a gate of a straight-line circuit with contamination delay $d \in \mathbb{R}$, given an earliest change time in $\mathbb{R} \cup \{\infty\}$ for every wire, the gate's earliest change is $d$ plus the minimum of the earliest changes of the wires it reads, where the minimum starts from $\infty$. A gate with no inputs therefore has computed earliest change $\infty$. For a causal gate output this means that the output is constant on $[0, \infty)$; times before $0$ are not constrained by the bound.
