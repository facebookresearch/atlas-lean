# The directed Hamiltonian cycle decision problem

The decision problem HAMILTONIAN CYCLE
(DIRECTED) accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to an instance $(n, E)$, consisting of a natural number $n$ and a finite list $E$ of
ordered pairs of natural numbers, such that $(n, E)$ is well formed ($n > 0$, $E$ has no
repeated entries, and every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$ and $u \ne v$) and
has a directed Hamiltonian cycle (a list $(v_0, \dots, v_{n-1})$ of $n$ distinct natural
numbers containing every natural number below $n$ such that $(v_j, v_{(j+1) \bmod n})$ occurs
in $E$ for every $j < n$). It rejects every bitstring that does not decode to an instance.
