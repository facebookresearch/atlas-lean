# Sequential composition of costed computations is associative

A cost is a triple of natural numbers (time, cumulative space, peak memory); costs add by adding
time and space and taking the maximum of the peak memories. A costed computation pairs a return
value with a cost. Write $x \gg\!= f$ for the computation that returns the value of $f(a)$, where
$a$ is the value of $x$, at the cost of $x$ plus the cost of $f(a)$. For every costed computation
$x$ and functions $f$ and $g$, $(x \gg\!= f) \gg\!= g = x \gg\!= (a \mapsto f(a) \gg\!= g)$.
