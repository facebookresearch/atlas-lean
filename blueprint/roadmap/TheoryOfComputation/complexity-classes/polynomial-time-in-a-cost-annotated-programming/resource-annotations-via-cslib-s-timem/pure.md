# Zero-cost computation

A cost is a triple of natural numbers (time, cumulative space, peak memory); costs add by adding
time and space and taking the maximum of the peak memories. A costed computation pairs a return
value with a cost. For a value $a$, the zero-cost computation returns $a$ at cost $0$.
