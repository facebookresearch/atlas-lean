# One polynomial bounds the reduction machine

Fix $r \in \mathbb{N}$, a finite TM2 machine
$M$ with an encoding $E$, a list $Y$ of input symbols of $M$, an output symbol $a$, a map $\iota$
from $\{0, \dots, r-1\}$ to input symbols, an input symbol $\mathit{sep}$, a polynomial $k$ with
coefficients in $\mathbb{N}$ and $c, e \in \mathbb{N}$. There is a polynomial $p$ with
coefficients in $\mathbb{N}$ such that for every raw input $s$, a list over
$\{0, \dots, r-1\}$, the reduction machine on input $s$ outputs the emitted formula for $s$
within $p(|s|)$ steps.
