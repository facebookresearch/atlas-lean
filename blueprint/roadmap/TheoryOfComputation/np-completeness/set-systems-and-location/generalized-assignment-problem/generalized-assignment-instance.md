# Generalized-assignment instances

A generalized-assignment instance is a tuple
$(R, C, c, K)$ where $R$ and $C$ are finite lists of finite lists of natural numbers, read as
matrices indexed by job and machine ($R_{j,i}$ is the resource job $j$ consumes on machine $i$
and $C_{j,i}$ is the cost of assigning job $j$ to machine $i$), $c$ is a finite list of natural
numbers (the machine capacities $c_i$), and $K$ is a natural number (the cost bound).
