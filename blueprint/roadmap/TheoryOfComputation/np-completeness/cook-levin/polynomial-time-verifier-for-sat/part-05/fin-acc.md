# The tokenizer accepts when the formula stack is empty

Let $w$, $t$, $b$ be lists of
symbols, $i, j \in \mathbb{N}$ and $v$ a bit. In exactly one step, the SAT tokenizer goes from the
label $\mathsf{fin}$ with internal bit $v$, empty formula stack $X$, stacks $W$, $T$, $B$ holding
$w$, $t$, $b$, and $i$ and $j$ marks on the clause and literal counters, to the label
$\mathsf{acc}$ with internal bit false and all stacks unchanged.
