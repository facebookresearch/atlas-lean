# Sequencing after a pure value applies the continuation

A cost is a triple of natural numbers: time, space and memory. Costs are added by adding time and space and taking the maximum of the memories. A cost-annotated computation returns a value together with an accumulated cost; returning a value accumulates zero cost, and sequencing two computations adds their costs. For every value $a$ and every function $f$ from values to cost-annotated computations, sequencing the computation that returns $a$ at zero cost with $f$ gives exactly $f(a)$.
