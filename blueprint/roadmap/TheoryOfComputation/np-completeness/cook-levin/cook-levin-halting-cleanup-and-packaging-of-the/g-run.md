# The reduction machine halts with the emitted formula

Fix $r \in \mathbb{N}$, a finite TM2
machine $M$ with an encoding $E$, a list $Y$ of input symbols of $M$, an output symbol $a$, a map
$\iota$ from $\{0, \dots, r-1\}$ to input symbols, an input symbol $\mathit{sep}$, a polynomial
$k$ with coefficients in $\mathbb{N}$ and $c, e \in \mathbb{N}$. For every raw input $s$, a list
over $\{0, \dots, r-1\}$, the program of the reduction machine goes in at most $g_B(|s|)$ steps
from the initial configuration on input $s$ to the halting configuration with output the emitted
formula for $s$ (no label, the initial state, that formula on the output stack and every other
stack empty), where $g_B$ is the step bound of the composed machine.

No assumption on the verifier data is needed.
