# Non-halting on zero reduces to totality

Writing $\varphi_c$ for the partial function on
$\mathbb{N}$ computed by a code $c$ of a partial recursive function, the set of codes $c$ with
$\varphi_c(0)$ undefined is many-one reducible to the set of total codes, the codes that halt on
every input: there is a computable function $f$ from codes to codes such that, for every code
$c$, $\varphi_c(0)$ is undefined if and only if $f(c)$ is total.
