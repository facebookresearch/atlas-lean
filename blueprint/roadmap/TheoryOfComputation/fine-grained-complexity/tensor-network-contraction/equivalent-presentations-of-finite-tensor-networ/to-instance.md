# Complete-graph instance of a factored network

Let $N$ be a factored tensor network on a finite linearly ordered vertex set $J$, and for each pair
$a, b$ let $D_{a,b}$ be a finite set of names in a type $A$ and $\delta_{a,b}$ a map from $A$ to the
labels of $N$. The complete-graph instance of $N$ has local tensors

$$R_a(\theta) = \sum_{z \in S_a} W_a(z) \prod_{b \ne a} g_{a,b}(z, \theta_b), \qquad \theta : J \to A,$$

where, writing $(a', b') = (\min(a,b), \max(a,b))$, the factor $g_{a,b}(z, \theta_b)$ is
$f_{a,b}(z, \delta_{a',b'}(\theta_b))$ if $\theta_b \in D_{a',b'}$ and $0$ otherwise.
