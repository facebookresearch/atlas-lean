# Started at $I_1$ with $x = x_0$, the scheme halts with final value $v$ in STRONG INEQUIVALENCE OF IANOV SCHEMES

In STRONG INEQUIVALENCE OF IANOV SCHEMES, started at $I_1$ with $x = x_0$, the scheme $S$ halts with final value $v$ when some finite number $n \ge 0$ of [execution steps](step.md) from the configuration $(0, x_0)$ reaches a configuration $(c, v)$ whose instruction is exactly the halt instruction, that is, the entry of $S$ at $0$-based index $c$ exists and equals $(2, 0, 0, 0)$.

A configuration that stops moving does not by itself halt. A scheme consisting only of the entry $(2, 1, 0, 0)$ never moves and never halts, and neither does a scheme whose control reaches an index with no entry.
