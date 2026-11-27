# Value of a factored tensor network

For a factored tensor network on a finite linearly ordered vertex set $J$, the value is the
integer

$$\sum_{z} \prod_{a \in J} W_a(z_a) \prod_{a < b} I_{a,b}(z_a, z_b),$$

where $z$ ranges over the assignments of a state $z_a \in S_a$ to every vertex $a$, the second
product is over the pairs of vertices $a < b$, and $I_{a,b}$ is the interaction.
