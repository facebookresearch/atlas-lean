# Charging twice is charging the sum

A cost is a triple of natural numbers: time, space and memory. Costs are added by adding time and space and taking the maximum of the memories. A cost-annotated computation returns a value together with an accumulated cost; returning a value accumulates zero cost, and sequencing two computations adds their costs. Charging a cost $c$ before a computation adds $c$ to its accumulated cost. For all costs $c_1, c_2$ and every computation $x$, charging $c_1$ before charging $c_2$ before $x$ is the same as charging the sum $c_1 + c_2$ before $x$.
