# Schönhage's asymptotic sum inequality

Suppose the direct sum $\bigoplus_{i=1}^{p} \langle n_i, m_i, k_i \rangle$ of matrix multiplication tensors has border rank at most $r$, where $r > p$. Then the matrix multiplication exponent satisfies

$$
\sum_{i=1}^{p} (n_i m_i k_i)^{\omega/3} \le r.
$$

## Proof sketch

Take the $N$-th tensor power of the direct sum, which by the multinomial theorem contains many copies of each product shape; border rank is submultiplicative and a border rank bound degenerates into a rank bound with polynomial overhead in $N$. Grouping the copies of the most frequent shape and using that $r'$ copies of $\langle a, b, c\rangle$ with border rank $r''$ give $\omega$ bounds via a recursive block algorithm yields the inequality as $N \to \infty$.

## Depends on

- [Matrix multiplication exponent](../matrix-multiplication-exponent/matrix-multiplication-exponent.md)
- [Matrix multiplication tensor](../matrix-multiplication-exponent/matrix-multiplication-tensor.md)

## Proof depends on

- [Schönhage's 1981 bound on the matrix multiplication exponent](../matrix-multiplication-exponent/schonhage1981-upper.md)

## Sources

- A. Schönhage, "Partial and total matrix multiplication", SIAM Journal on Computing 10 (1981) 434-455.
