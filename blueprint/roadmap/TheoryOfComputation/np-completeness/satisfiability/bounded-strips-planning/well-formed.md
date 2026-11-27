# Well-formed BOUNDED STRIPS PLANNING instances

An instance $(N, O, I, (G_+, G_-), k)$ of BOUNDED STRIPS PLANNING is well-formed when, for every operator, its preconditions $(o_+, o_-)$ and its postconditions $(o^+, o^-)$ are satisfiable conjunctions over $0, \dots, N-1$; every condition of $I$ is below $N$; the goals form a satisfiable conjunction; and every entry of the unary bound is true.
