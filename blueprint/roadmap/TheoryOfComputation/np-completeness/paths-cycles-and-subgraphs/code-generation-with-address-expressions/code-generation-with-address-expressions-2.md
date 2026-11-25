# Feasible CODE GENERATION WITH ADDRESS EXPRESSIONS instances

An instance $(g, B, C, M)$ is feasible when some one-to-one, order-preserving assignment $f$ of addresses in $\{1, \dots, M\}$ to the instructions gives every instruction $I_i$ either $-C < f(I_i) - h(I_i) < B$ (a one-byte instruction) or $f(I_i) + 1 \le M$ with $f(I_i) + 1$ assigned to no instruction (room for a two-byte instruction).
