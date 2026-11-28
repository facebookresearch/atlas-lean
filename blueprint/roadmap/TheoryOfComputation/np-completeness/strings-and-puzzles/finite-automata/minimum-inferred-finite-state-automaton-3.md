# Feasible instances of MINIMUM INFERRED FINITE STATE AUTOMATON

An instance $(m, S, T, K)$ is feasible when some deterministic finite automaton over the alphabet $\{0, \dots, m - 1\}$ with $K$ states accepts every word over that alphabet that is listed in $S$ and rejects every such word listed in $T$. Listed strings that use a letter $\ge m$ impose no condition: for $m = K = 1$, listing $[1]$ in both $S$ and $T$ still leaves the instance feasible. Well-formed instances list only words over the alphabet.
