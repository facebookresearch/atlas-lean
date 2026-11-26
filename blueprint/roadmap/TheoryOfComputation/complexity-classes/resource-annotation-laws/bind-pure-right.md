# Sequencing with a pure return changes nothing

A cost is a triple of natural numbers: time, space and memory. Costs are added by adding time and space and taking the maximum of the memories. A cost-annotated computation returns a value together with an accumulated cost; returning a value accumulates zero cost, and sequencing two computations adds their costs. For every cost-annotated computation $x$, sequencing $x$ with the computation that returns its result at zero cost gives back $x$.
