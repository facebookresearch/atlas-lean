# Evaluating a construction state

For a state of Cooper's construction and an assignment $\sigma$ of Booleans to variables, the node values are computed in the order the nodes were emitted: a node whose index occurs in the state's list of recorded (variable, node) pairs takes the value $\sigma(x)$, where $x$ is the variable of the first pair in the list with that node index, and every other node takes its forced value given the values of the earlier nodes.

The definition applies to any state; it does not assume that each node is recorded only once. If the list is $[(1, 0), (2, 0)]$, node $0$ takes the value $\sigma(1)$ even though it is also recorded for variable $2$.
