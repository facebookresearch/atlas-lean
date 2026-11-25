# Travel time along a tree edge

For an instance $(P, R, K)$ of VEHICLE SCHEDULING ON TREE and natural numbers $a, b$, write $(p_k, f_k, b_k)$ for entry $k$ of the parent list $P$, taken to be $(0, 0, 0)$ when $k$ is not less than the length of $P$. The travel time from $a$ to $b$ is

$$\mathrm{travel}(a, b) = \begin{cases} f_{b-1} & \text{if } b > 0 \text{ and } p_{b-1} = a, \\ b_{a \mathbin{\dot-} 1} & \text{otherwise,} \end{cases}$$

where $a \mathbin{\dot-} 1$ is truncated subtraction ($0 \mathbin{\dot-} 1 = 0$). For a tree edge, this is the forward time when $a$ is the parent of $b$ and the backward time when $b$ is the parent of $a$.
