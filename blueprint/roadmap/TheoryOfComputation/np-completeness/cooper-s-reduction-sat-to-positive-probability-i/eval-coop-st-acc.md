# The built network evaluates the formula

For every CNF formula $\varphi$ and assignment $\sigma$ of Booleans to its variables, the accumulator node of the network Cooper's construction builds for $\varphi$ evaluates under $\sigma$ to true exactly when every clause of $\varphi$ is true under $\sigma$. Each clause component evaluates to its clause's value, and the AND chain collects these values.
