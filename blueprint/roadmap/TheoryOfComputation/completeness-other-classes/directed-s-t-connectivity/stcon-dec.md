# Directed $s$-$t$ connectivity

The decision problem of directed $s$-$t$ connectivity
accepts a bitstring $x$ exactly when decoding $x$ with the canonical bitstring encoding of
tuples $(n, E, s, t)$, where $n$, $s$ and $t$ are natural numbers and $E$ is a list of pairs of
natural numbers, succeeds and gives a tuple such that $s < n$, $t < n$, and there are pairwise
distinct natural numbers $v_0, \dots, v_k$, all less than $n$, with $v_0 = s$, $v_k = t$ and
$(v_j, v_{j+1}) \in E$ for every $j < k$. Bitstrings that do not decode are rejected.
