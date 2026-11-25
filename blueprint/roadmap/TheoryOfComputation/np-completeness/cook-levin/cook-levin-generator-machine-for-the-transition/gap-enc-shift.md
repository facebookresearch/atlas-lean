# Shifting the start of a gap encoding

Let $m \le m'$ and let
$\ell = [(p_1, b_1), \dots, (p_n, b_n)]$ be a list of literals with
$m' \le p_1 < \dots < p_n < V$ (if $\ell$ is empty, require $m' \le V$). Then the gap encoding
of $\ell$ from slot $m$ to $V$ is $m' - m$ copies of the absent-slot block $01$ followed by the
gap encoding of $\ell$ from slot $m'$ to $V$.
