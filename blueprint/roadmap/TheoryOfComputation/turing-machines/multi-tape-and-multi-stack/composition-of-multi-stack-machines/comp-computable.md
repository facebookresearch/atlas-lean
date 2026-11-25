# The composite polynomial-time multi-stack computation

A polynomial-time multi-stack computation of a function $f : \alpha \to \beta$ with respect to
encodings $e_\alpha$ and $e_\beta$ of $\alpha$ and $\beta$ as words over alphabets $\Gamma_\alpha$
and $\Gamma_\beta$ consists of a finite multi-stack Turing machine, a bijection between the
alphabet of its input stack and $\Gamma_\alpha$, a bijection between the alphabet of its output
stack and $\Gamma_\beta$, and a time bound $p \in \mathbb{N}[X]$, such that for every
$a \in \alpha$ the machine, started on $e_\alpha(a)$ written in its input alphabet, reaches within
$p(|e_\alpha(a)|)$ steps the halting configuration whose output stack holds $e_\beta(f(a))$
written in its output alphabet.

Let $h_1$ be a polynomial-time multi-stack computation of $f : \alpha \to \beta$ with respect to
$e_\alpha$ and $e_\beta$, and $h_2$ one of $g : \beta \to \gamma$ with respect to $e_\beta$ and
$e_\gamma$. The composite computation is the polynomial-time multi-stack computation of
$g \circ f$ with respect to $e_\alpha$ and $e_\gamma$ whose machine is the composite machine of
the machines of $h_1$ and $h_2$ with the symbol translation between them, whose input alphabet
bijection is that of $h_1$, whose output alphabet bijection is that of $h_2$, and whose time bound
is the composite time bound of $h_1$ and $h_2$.

In particular, functions computable in polynomial time by finite multi-stack Turing machines are
closed under composition.
