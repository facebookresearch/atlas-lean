# The formula emitted on a raw input

Fix $r \in \mathbb{N}$, a finite TM2 machine $M$ with
an encoding $E$, a list $Y$ of input symbols of $M$, an output symbol $a$, a map $\iota$ from
$\{0, \dots, r-1\}$ to input symbols, an input symbol $\mathit{sep}$, a polynomial $k$ with
coefficients in $\mathbb{N}$ and $c, e \in \mathbb{N}$. For a raw input $s$, a list over
$\{0, \dots, r-1\}$, let $x$ be $s$ with each symbol mapped by $\iota$, followed by
$\mathit{sep}$, let $m = |s| + 1 + k(|s|)$ and $T = (m + c)^e$. The emitted formula for $s$ is
the bit-string encoding of the assembled Cook–Levin formula $\Phi_E(x, Y, a, m, T)$.
