# The walk check after the first vertex

Let $s, t, n$ be natural numbers and $E$ a list of
pairs of natural numbers. For every list $q = (q_1, \dots, q_k)$ of natural numbers and all
natural numbers $c \neq 0$ and $b$, the walk check for $s, t, n, E$ accepts $q$ after $c$ vertices
the last of which was $b$ if and only if every $q_i$ is less than $n$, every pair $(u, v)$ of
consecutive entries of the list $(b, q_1, \dots, q_k)$ is an entry of $E$, the entries of $q$ are
pairwise distinct, $c + k = n$, and the last entry of $(b, q_1, \dots, q_k)$ is $t$.
