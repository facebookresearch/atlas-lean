# Payload normalization agrees with decode-then-encode

Read a bit string $x = x_0 x_1 \cdots x_{m-1}$ as a natural number $D(x)$ least significant bit first, where a
trailing $0$ is read as if a $1$ followed it:

$$
D(x) = \begin{cases} \sum_{i<m} x_i 2^i & \text{if } x \text{ is empty or ends with } 1,\\ \sum_{i<m} x_i 2^i + 2^m & \text{if } x \text{ ends with } 0 \end{cases}
$$

(so $D(0) = 2$). For every bit string $x$, the [normalization](normalize-nat.md) of $x$ is the binary code of
$D(x)$.
