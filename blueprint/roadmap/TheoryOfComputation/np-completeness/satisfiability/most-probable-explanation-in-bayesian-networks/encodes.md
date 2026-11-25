# Encodes

The Bayesian network $b$ has the structure and tables listed in the instance: for every node
$k$, the parents of $k$ are exactly the listed parents (all earlier in the topological order),
and for every listed table row $(u, \theta)$ and every instantiation $y$ of the parents of $k$
that agrees with $u$, the conditional distribution of node $k$ given $y$ assigns to each value
$v$ the probability $a / b$, where $(a, b)$ is entry $v$ of $\theta$ (a missing entry reads as
$(0, 1)$, probability $0$).
