# Symbol translation between composed machines

Let $h_1$ be a polynomial-time TM2
computation of $f : \alpha \to \beta$ and $h_2$ one of $g : \beta \to \gamma$, where $\beta$ is
encoded by lists over an alphabet $\Gamma_\beta$. A symbol $y$ of the output-stack alphabet of
$h_1$'s machine is sent to the symbol of the input-stack alphabet of $h_2$'s machine that
corresponds, under $h_2$'s input alphabet bijection with $\Gamma_\beta$, to the letter that $y$
corresponds to under $h_1$'s output alphabet bijection with $\Gamma_\beta$.
