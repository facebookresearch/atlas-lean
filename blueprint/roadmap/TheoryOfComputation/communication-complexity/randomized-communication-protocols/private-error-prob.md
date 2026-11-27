# Error probability of a private-coin protocol

Let $X$, $Y$ be sets and $R_A$, $R_B$ nonempty finite sets (private random strings of Alice and Bob). For a
deterministic protocol $p$ in which Alice holds $(x, a) \in X \times R_A$ and Bob holds $(y, b) \in Y \times R_B$,
a function $f : X \times Y \to \{0, 1\}$ and $(x, y) \in X \times Y$, the private error probability is the rational
number

$$\frac{|\{(a, b) \in R_A \times R_B : \text{the output of } p \text{ on } ((x, a), (y, b)) \text{ differs from } f(x, y)\}|}{|R_A|\,|R_B|},$$

the probability of an error when $a$ and $b$ are independent and uniform.
