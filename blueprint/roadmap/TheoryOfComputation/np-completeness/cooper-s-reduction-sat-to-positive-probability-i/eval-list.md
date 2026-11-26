# Evaluating a construction state

For a state of Cooper's construction and an assignment $\sigma$ of Booleans to variables, the node values are computed in the order the nodes were emitted: a node recorded as the root of a variable $x$ takes the value $\sigma(x)$, and every other node takes its forced value given the values of the earlier nodes.
