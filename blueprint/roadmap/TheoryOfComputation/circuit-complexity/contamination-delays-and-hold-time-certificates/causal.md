# Causal gate-delay model for one gate, after the clock edge

A gate with contamination delay $d \in \mathbb{R}$ and output signal $\mathit{out} : \mathbb{R} \to U$ follows the causal model when $d \ge 0$ and, for every $\tau \in \mathbb{R} \cup \{\infty\}$, if every wire the gate reads is stable on $[0, \tau)$, then its output is stable on $[0, d + \tau)$. A gate with no inputs is therefore constant after the clock edge at time $0$. Only times from the edge on are constrained; the model says nothing about whether the output had settled before the edge.
