# Farthest string as distinguishing string selection

The DISTINGUISHING STRING SELECTION instance of a FARTHEST STRING instance $(q, L, S, d)$ is the six-field tuple $(q, L, [\,], S, 0, d)$: the same alphabet size $q$ and string length $L$, no bad strings, the given strings $S$ as good strings, close threshold $0$ and far threshold $d$. The first two fields matter: they fix the witness alphabet and comparison length, so for $(2, 1, [[0]], 1)$ the word $[1]$ is a witness, and changing the alphabet size to $1$ would remove every witness.
