# Serial gate evaluation agrees with typed gate evaluation

For every list $v$ of Boolean
values of earlier gates, every assignment of Boolean values to the $n$ inputs and every pair
$g = (k, r)$ of a natural number $k$ (the gate kind) and a list $r$ of natural numbers (its
references), evaluating $g$ with the serial $(\mathrm{kind}, \mathrm{refs})$ gate evaluator
gives the same value as evaluating the gate decoded from $g$ with the gate-value function.
