# Error recursion for concatenated fault-tolerant codes

Let $c > 0$ and let $(p_j)_{j \ge 0}$ be a sequence of nonnegative reals with $p_0 = p$ and
$p_{j+1} \le c\, p_j^2$ for all $j \ge 0$. Then

$$p_k \le \frac{(cp)^{2^k}}{c} \quad\text{for every integer } k \ge 0.$$

Consequently, if $0 < cp < 1$ and $0 < c\varepsilon < 1$, then $p_k \le \varepsilon$ for every integer
$k \ge \log_2\big(\log(c\varepsilon)/\log(cp)\big)$, so $k = O(\log\log(1/\varepsilon))$ levels suffice. If $p = 0$
then $p_k = 0$ for all $k \ge 1$, and if $\varepsilon \ge 1/c$ and $cp < 1$ then $k = 0$ already gives
$p_0 = p < 1/c \le \varepsilon$.

In the analysis of concatenated fault-tolerant codes, $p_j$ bounds the failure probability of a level-$j$ gadget and
the recursion is the inequality supplied by the analysis of one level of concatenation; this lemma is only the
arithmetic step of the threshold theorem.

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §21.6. <https://arxiv.org/pdf/1907.09415v6>
