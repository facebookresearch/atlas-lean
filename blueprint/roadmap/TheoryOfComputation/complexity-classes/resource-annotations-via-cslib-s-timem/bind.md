# Sequential composition of costed computations

A cost is a triple of natural numbers (time, cumulative space, peak memory); costs add by adding
time and space and taking the maximum of the peak memories. A costed computation pairs a return
value with a cost. For a costed computation $x$ and a function $f$ from values to costed
computations, their sequential composition returns the value of $f$ applied to the value of $x$, at
the cost of $x$ plus the cost of that computation.
