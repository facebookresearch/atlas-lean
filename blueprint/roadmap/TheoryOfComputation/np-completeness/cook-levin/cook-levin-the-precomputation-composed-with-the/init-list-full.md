# Initial configuration of the full machine

Let $E$ be encoding data for a finite
multi-stack Turing machine $M$, and let $r$ be a natural number. Fix a list $Y$ of input-stack
symbols of $M$, an output-stack symbol $a$ of $M$, a map $\iota$ from $\{0, \dots, r-1\}$ to
input-stack symbols of $M$, a separator input-stack symbol $\sigma$ of $M$, a polynomial $k$ with
natural-number coefficients and natural numbers $c$ and $e$. On every raw input $s$, a word over
$\{0, \dots, r-1\}$, the initial configuration of the full machine built from these data is at
the read-loop label with internal state false, its raw-input stack holds $s$, and all its other
stacks (the code stack, the output stack, the scratch counters and the remaining host stacks)
are empty.
