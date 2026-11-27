# Time-bounded Kolmogorov complexity K^t and Levin's Kt

Fix a universal multi-tape Turing machine $U$ that parses a binary program $p$ as the description of a machine and simulates it. For $t : \mathbb{N} \to \mathbb{N}$ and $x \in \{0,1\}^*$, the *time-bounded Kolmogorov complexity* is

$$K^t(x) = \min\{|p| : U(p) \text{ outputs } x \text{ within } t(|x|) \text{ steps}\},$$

and *Levin's* complexity is $Kt(x) = \min\{|p| + \lceil \log_2 \tau \rceil : U(p) \text{ outputs } x \text{ within } \tau \text{ steps}\}$. Always $K(x) \le K^t(x)$, $K^t$ is antitone in $t$, $K^t(x) \le |x| + O(1)$ for $t(n) \ge c\,n$, and $K(x) \le Kt(x)$. Conditional versions $K^t(x \mid y)$ and $Kt(x \mid y)$ give $y$ to the machine as auxiliary input.

## Depends on

- [Kolmogorov complexity](../k.md)
- [The universal description method](../u.md)

## Sources

- M. Li and P. Vitányi, "An Introduction to Kolmogorov Complexity and Its Applications", 4th ed., Springer, 2019.
- L. A. Levin, "Universal Sequential Search Problems", Problems of Information Transmission 9(3), 1973.
- K.-I. Ko, "On the Complexity of Learning Minimum Time-Bounded Turing Machines", SIAM Journal on Computing 20(5), 1991.
- S. Hirahara, "Non-Black-Box Worst-Case to Average-Case Reductions within NP", FOCS 2018.
