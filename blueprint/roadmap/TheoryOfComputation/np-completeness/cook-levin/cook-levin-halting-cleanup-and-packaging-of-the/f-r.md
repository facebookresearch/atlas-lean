# The Cook–Levin reduction function

Fix $r \in \mathbb{N}$, a finite TM2 machine $M$ with
an encoding $E$, a list $Y$ of input symbols of $M$, an output symbol $\mathrm{acc}$ of $M$, a
map $\iota$ from $\{0, \dots, r-1\}$ to input symbols of $M$, an input symbol $\mathit{sep}$ of
$M$, a polynomial $k$ with coefficients in $\mathbb{N}$ and $c, e \in \mathbb{N}$. Let
$\mathit{ea}$ encode the elements of a type $\alpha$ as lists over an alphabet $\Sigma$, and let
$\mathit{eqv}$ be a bijection from $\{0, \dots, r-1\}$ to $\Sigma$. The reduction function sends
$u \in \alpha$ to the emitted formula for the raw input $s$ obtained by applying
$\mathit{eqv}^{-1}$ to each symbol of $\mathit{ea}(u)$: the dense encoding of the assembled
Cook–Levin formula $\Phi_E(x, Y, \mathrm{acc}, m, T)$, where $x$ is $s$ with each symbol mapped
by $\iota$, followed by $\mathit{sep}$, $m = |s| + 1 + k(|s|)$ and $T = (m + c)^e$.
