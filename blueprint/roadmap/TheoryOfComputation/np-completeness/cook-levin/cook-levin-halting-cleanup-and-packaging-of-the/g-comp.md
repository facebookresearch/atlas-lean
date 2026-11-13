# The reduction machine as a polynomial-time computation

Fix $r \in \mathbb{N}$, a finite
TM2 machine $M$ with an encoding $E$, a list $Y$ of input symbols of $M$, an output symbol $a$, a
map $\iota$ from $\{0, \dots, r-1\}$ to input symbols, an input symbol $\mathit{sep}$, a
polynomial $k$ with coefficients in $\mathbb{N}$ and $c, e \in \mathbb{N}$. Let $\mathit{ea}$
encode the elements of a type $\alpha$ as lists over an alphabet $\Sigma$, and let $\mathit{eqv}$
be a bijection from $\{0, \dots, r-1\}$ to $\Sigma$. This is a polynomial-time TM2 computation of
the reduction function $f_R$, which sends $u \in \alpha$ to the emitted formula for the raw input
obtained by applying $\mathit{eqv}^{-1}$ to each symbol of $\mathit{ea}(u)$, from the encoding
$\mathit{ea}$ to the identity encoding of bit strings: the machine is the reduction machine, its
input alphabet is identified with $\Sigma$ by $\mathit{eqv}$, its output alphabet with the
Booleans by the identity, and its time bound is a polynomial $p$ with $p(n) = g_B(n)$ for all
$n$, where $g_B$ is the step bound of the composed machine.
