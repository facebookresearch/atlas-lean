# Time bound of the canonical simulation

For a time bound $t : \mathbb{N} \to \mathbb{N}$, the canonical time bound is the function $n \mapsto 4\,t(n) + 2n + 10$. If a code decides $L$ within $t$, its canonical simulation on an encoded binary word of length $n$ outputs the answer within this many steps, including cleanup.
