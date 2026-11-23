# Cost of a randomized protocol

A randomized protocol for inputs $X$ (Alice) and $Y$ (Bob) is a probability distribution $\pi$ with finite support on deterministic two-party protocols for $X$ and $Y$ (finite binary trees whose internal nodes are owned by Alice or Bob and labelled by maps $X \to \{0,1\}$ or $Y \to \{0,1\}$, and whose leaves carry output bits; the depth is the largest number of bits announced along a root-to-leaf path).
The cost of $\pi$ is the largest depth of a protocol in the support of $\pi$, and $0$ if the support
is empty.
