# Real input vector of an example in TRAINING A 3-NODE NEURAL NETWORK

In TRAINING A 3-NODE NEURAL NETWORK, for a number $n$ of inputs and a list $x$ of Booleans, the real input vector is $(z_0, \ldots, z_{n-1}) \in \mathbb{R}^n$ with $z_j = 1$ if entry $j$ of $x$ is true and $z_j = 0$ otherwise. A list shorter than $n$ is padded with zeros (a missing entry reads as false), and the entries of $x$ after the first $n$ are ignored.
