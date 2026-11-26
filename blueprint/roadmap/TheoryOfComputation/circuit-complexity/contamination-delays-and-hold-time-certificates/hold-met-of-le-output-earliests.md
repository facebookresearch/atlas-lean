# Hold certificate

Let a circuit with real contamination delays follow the causal gate-delay model, and let its inputs be launched by a register clocked at time $0$, so that every input signal is stable on $[0, t_q)$, where $t_q \ge 0$ is the minimum clock-to-Q delay. Let $\mathit{hold}, u \ge 0$ be the hold time and clock uncertainty, and let $e_o$ be the computed earliest change of output $o$ when every input's earliest change is $0$. If $\mathit{hold} + u \le t_q + e_o$, then the signal of output $o$ passes the receiving register's hold check: it is stable on $[0, \mathit{hold} + u)$.
