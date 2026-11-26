# Feasible CODE GENERATION WITH UNFIXED VARIABLE LOCATIONS instances

An instance $(m, g, B, M)$ is feasible when some one-to-one assignment $f$ of locations in $\{1, \dots, M\}$ to the instructions and variables, increasing on the instructions in their order, gives every instruction $I_i$ either $|f(I_i) - f(g(I_i))| < B$ (a one-byte instruction) or $f(I_i) + 1 \le M$ with $f(I_i) + 1$ assigned to nothing (room for a two-byte instruction).
