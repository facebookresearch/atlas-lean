# Symbol translation between composed machines

Let $h_1$ be a polynomial-time multi-stack computation of $f : \alpha \to \beta$ and $h_2$ one of
$g : \beta \to \gamma$, where $\beta$ is encoded by words over an alphabet $\Gamma_\beta$ (so
$h_1$ has a bijection between the alphabet of its output stack and $\Gamma_\beta$, and $h_2$ a
bijection between the alphabet of its input stack and $\Gamma_\beta$). A symbol $y$ of the
output-stack alphabet of $h_1$'s machine is sent to the symbol of the input-stack alphabet of
$h_2$'s machine that corresponds, under $h_2$'s input alphabet bijection, to the letter of
$\Gamma_\beta$ that $y$ corresponds to under $h_1$'s output alphabet bijection.
