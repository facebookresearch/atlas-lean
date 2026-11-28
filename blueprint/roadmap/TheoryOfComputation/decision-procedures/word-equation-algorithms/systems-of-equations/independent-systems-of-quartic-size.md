# Independent systems can have quartic size

Over $n = 4m$ unknowns there are independent systems of constant-free word equations with a nonperiodic solution and $m^2(m-1)(m-2)/6$ equations, so independent systems can have size of order $n^4$.

Let $m \ge 1$, take the $n = 4m$ unknowns $x_r, y_r, z_r, t_r$ for $1 \le r \le m$, and let $\Sigma$ be an alphabet with two distinct letters $a, b$. For $i, j, k, l \in \{1, \dots, m\}$ with $i < j < k$ let $E(i, j, k, l)$ be the constant-free equation

$$
x_i x_j x_k\, y_i y_j y_k\, z_i z_j z_k\, t_l \;=\; t_l\, x_i x_j x_k\, y_i y_j y_k\, z_i z_j z_k .
$$

The system of all these equations is an [independent system](independent-systems-of-word-equations.md) with a nonperiodic solution in $\Sigma^*$, and it has $\binom{m}{3} m = m^2 (m-1)(m-2)/6$ equations. Hence

$$
\mathrm{IS}'(4m) \ge \frac{m^2 (m-1)(m-2)}{6} .
$$

The bound is positive for $m \ge 3$ and is asymptotically $n^4 / 1536$; it is a lower bound only.

## Depends on

- [Independent systems of constant-free word equations](independent-systems-of-word-equations.md)

## Proof depends on

- [Commuting words are powers of a common word](../../word-equations-with-length/commuting-words-are-powers-of-a-common-word.md)

## Expansion

Sending every $t_l$ to the empty word, $x_1 \mapsto a$, $y_1 \mapsto b$, and every other unknown to the empty word gives a nonperiodic solution of every equation. For independence fix $(i, j, k, l)$ and let $h$ send $x_r \mapsto ab$, $y_r \mapsto a$, $z_r \mapsto ba$ for $r \in \{i, j, k\}$, $t_l \mapsto ababa$, and every other unknown to the empty word. For an equation $E(i', j', k', l')$ with $l' \neq l$ both sides have the same image. If $l' = l$ and $s$ of the indices $i', j', k'$ lie in $\{i, j, k\}$, the equation asks that $W_s = (ab)^s a^s (ba)^s$ commute with $ababa$. For $s < 3$, $W_s = (ababa)^s$, so the equation holds. For $s = 3$, which happens only for $E(i, j, k, l)$ itself, $W_3$ and $(ababa)^3$ have the same length $15$ but differ; since $ababa$ is primitive (its length $5$ is prime and it is not a power of a letter), a word commuting with it is a power of it, and a power of length $15$ would be $(ababa)^3$; so $h$ does not solve $E(i, j, k, l)$. The construction modifies one of J. Karhumäki and W. Plandowski, which gives $\mathrm{IS}(n) = \Omega(n^4)$ with $n = 10m$ unknowns.

## Sources

- Juhani Karhumäki, Aleksi Saarela, "On maximal chains of systems of word equations", Proceedings of the Steklov Institute of Mathematics 274 (2011), 116–123, https://doi.org/10.1134/S0081543811060083; read as arXiv:1506.02913v1, https://arxiv.org/abs/1506.02913v1, Theorem 6.1 and its proof (Section 6, "Lower Bounds")
- Aleksi Saarela, "Systems of word equations, polynomials and linear algebra: A new approach", European Journal of Combinatorics 47 (2015), 1–14, https://doi.org/10.1016/j.ejc.2015.01.005; read as arXiv:1401.7498v1, https://arxiv.org/abs/1401.7498v1, Section 1
