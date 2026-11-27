# Instances of DISTANCE-d PARTITION OF POINTS IN THE PLANE

An instance of DISTANCE-d PARTITION OF POINTS IN THE PLANE is an ordered list of sites, repetitions allowed, each a pair of natural pairs `((a, b), (c, d))` read as the point $(a - b, c - d) \in \mathbb{Z}^2$. Different pairs can encode the same coordinate: `(0, 0)` and `(1, 1)` both encode $0$, and a repeated origin is still two entries. The instance also stores two natural numbers, the distance $d$ and the number of sets $K$. Distinct sites, and the other conditions of the usual problem, belong to [validation](well-formed.md).
