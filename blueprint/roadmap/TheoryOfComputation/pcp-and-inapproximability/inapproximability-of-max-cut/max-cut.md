# MAX-CUT as an optimization problem

MAX-CUT is the optimization problem whose instances
are bitstrings $x$, read as an adjacency matrix on $n = \lfloor \sqrt{|x|} \rfloor$ vertices in
which, for $i < j < n$, bit $i n + j$ of $x$ (bits indexed from $0$) says whether $\{i, j\}$ is
an edge. Its feasible solutions for $x$ are the bitstrings of length $n$, one bit per vertex;
the value of a feasible solution $s$ is the number of pairs $i < j < n$ that are edges and
whose bits in $s$ differ, the value of an infeasible solution is $0$, and the polynomial bound
on the length of feasible solutions is $p(m) = m$.

## Sources

- C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and complexity classes", Journal of Computer and System Sciences 43 (1991), 425-440.
