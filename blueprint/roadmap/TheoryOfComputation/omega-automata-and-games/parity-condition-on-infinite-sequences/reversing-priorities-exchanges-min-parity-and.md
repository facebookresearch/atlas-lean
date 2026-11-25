# Reversing priorities exchanges the min-parity and max-parity conditions

Let $(p_k)_{k \in \mathbb{N}}$ be a sequence of natural numbers with $p_k \le d$ for every $k$, and let $D \ge d$ be even. The sequence satisfies the *even min-parity condition* if the least value occurring infinitely often in $(p_k)$ is even. Then $(p_k)$ satisfies the even min-parity condition if and only if the sequence $(D - p_k)_{k \in \mathbb{N}}$ satisfies the even max-parity condition.

Since the $p_k$ lie in the finite set $\{0, \dots, d\}$, the set $I$ of values occurring infinitely often in $(p_k)$ is nonempty. The map $p \mapsto D - p$ is an order-reversing bijection of $\{0, \dots, D\}$ that preserves parity because $D$ is even; it maps $I$ onto the set of values occurring infinitely often in $(D - p_k)$, and the least element of $I$ to the largest element of that set.

## Depends on

- [Even max-parity condition](parity-even.md)

## Sources

- M. Jurdziński, "Small progress measures for solving parity games", *STACS 2000*, LNCS 1770, Springer, 2000, Section 1 (the winner of a play is decided by the parity of the lowest priority occurring infinitely often)
