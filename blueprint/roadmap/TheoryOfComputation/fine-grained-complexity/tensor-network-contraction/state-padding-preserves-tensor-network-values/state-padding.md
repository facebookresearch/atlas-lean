# State padding of a factored tensor network

Let $N_0$ and $N_1$ be factored tensor networks on the same linearly ordered vertex set, with
states in $\sigma_0$ and $\sigma_1$ and labels in the same type, and let $\pi_a : \sigma_0 \to
\sigma_1$ be a map for each vertex $a$. Then $\pi$ is a state padding of $N_0$ into $N_1$ when

- $\pi_a(z) \in S^1_a$ for every $z \in S^0_a$;
- $\pi_a$ is injective on $S^0_a$;
- every state $y \in S^1_a$ that is not $\pi_a(z)$ for any $z \in S^0_a$ has weight $W^1_a(y) = 0$;
- $W^1_a(\pi_a(z)) = W^0_a(z)$ for every $z \in S^0_a$;
- for distinct $a, b$, $z \in S^0_a$ and $z' \in S^0_b$, the interactions satisfy
  $I^1_{a,b}(\pi_a(z), \pi_b(z')) = I^0_{a,b}(z, z')$;
- for distinct $a, b$, the capacities satisfy $c^1_{a,b} = c^0_{a,b}$;
- for distinct $a, b$, $z \in S^0_a$ and $\theta$ in the label set of $\{a, b\}$ in $N_0$, the
  factors satisfy $f^1_{a,b}(\pi_a(z), \theta) = f^0_{a,b}(z, \theta)$.
