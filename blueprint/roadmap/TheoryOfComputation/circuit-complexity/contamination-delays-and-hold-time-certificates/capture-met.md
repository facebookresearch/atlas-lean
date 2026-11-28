# Capture check at the receiving register

For a register clocked at time $0$ with nonnegative setup time $\mathit{setup}$, hold time $\mathit{hold}$ and clock uncertainty $u$, the capture check holds for a data signal $s : \mathbb{R} \to U$ when $s(t) = s(0)$ for every $t$ with $-(\mathit{setup} + u) \le t < \mathit{hold} + u$.
