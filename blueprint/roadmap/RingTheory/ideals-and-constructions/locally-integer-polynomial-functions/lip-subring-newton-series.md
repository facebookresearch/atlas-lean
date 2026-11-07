# Newton series of locally integer polynomial functions

Let $U \subseteq \mathbb{Z}$, let
$\mathbb{N} = \{0, 1, 2, \dots\}$, and let $\sigma : \mathbb{N} \to U$ be a bijection. For a
sequence of integers $a = (a_k)_{k \in \mathbb{N}}$ define $f_a : U \to \mathbb{Z}$ by

$$f_a(u) = \sum_{k=0}^{\sigma^{-1}(u)} a_k \prod_{i=0}^{k-1} (u - \sigma(i)).$$

Then $f_a$ lies in the ring $\mathrm{LIP}(U)$ of locally integer polynomial functions on $U$ for
every sequence $a$, and every $f \in \mathrm{LIP}(U)$ equals $f_a$ for exactly one sequence $a$.

For $u = \sigma(m)$ every product with $k > m$ contains the factor $u - \sigma(m) = 0$, so $f_a$
is the formal series $\sum_{k \ge 0} a_k \prod_{i < k} (x - \sigma(i))$ evaluated at $x = u$.

## Sources

- Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025), Article A41, Theorem 1, reindexed from `σ(1), σ(2), …`.
