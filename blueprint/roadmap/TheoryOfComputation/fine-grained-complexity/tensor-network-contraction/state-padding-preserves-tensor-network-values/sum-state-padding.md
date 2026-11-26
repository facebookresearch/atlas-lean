# State padding preserves the weighted pair sum

Let $J$ be a finite linearly ordered set. For $i = 0, 1$ let $S^i_a$ be finite sets of states in a
type $\sigma_i$, $W^i_a$ integer weights and $K^i_{a,b}$ integer pair kernels, and let
$\pi_a : \sigma_0 \to \sigma_1$ be maps such that

- $\pi_a(z) \in S^1_a$ for every $z \in S^0_a$, and $\pi_a$ is injective on $S^0_a$;
- every $y \in S^1_a$ outside the image of $S^0_a$ under $\pi_a$ has $W^1_a(y) = 0$;
- $W^1_a(\pi_a(z)) = W^0_a(z)$ for every $z \in S^0_a$;
- $K^1_{a,b}(\pi_a(z), \pi_b(z')) = K^0_{a,b}(z, z')$ for distinct $a, b$, $z \in S^0_a$ and
  $z' \in S^0_b$.

Then

$$\sum_{y} \prod_{a} W^1_a(y_a) \prod_{a < b} K^1_{a,b}(y_a, y_b) = \sum_{z} \prod_{a} W^0_a(z_a) \prod_{a < b} K^0_{a,b}(z_a, z_b),$$

where $y$ ranges over the assignments with $y_a \in S^1_a$ for all $a$ and $z$ over those with
$z_a \in S^0_a$.
