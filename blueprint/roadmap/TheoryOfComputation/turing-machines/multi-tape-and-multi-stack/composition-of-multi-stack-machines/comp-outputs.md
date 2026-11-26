# The composite machine computes the composite function in time

Let $M_1$ compute
$f : \alpha \to \beta$ in polynomial time from the encoding $e_\alpha$ to $e_\beta$, and let $M_2$
compute $g : \beta \to \gamma$ in polynomial time from $e_\beta$ to $e_\gamma$. For every
$a \in \alpha$, let $n$ be the length of $e_\alpha(a)$ and $T$ the composite time bound. Started on
$e_\alpha(a)$, written in the input alphabet of $M_1$, the composite machine of $M_1$ and $M_2$
(with the glue map from output symbols of $M_1$ to input symbols of $M_2$) reaches within
$T(n)$ steps the halted configuration whose output stack holds $e_\gamma(g(f(a)))$, written in the
output alphabet of $M_2$, whose other stacks are empty and whose internal state is the initial
one.
