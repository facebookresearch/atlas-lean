# The complexity class NEXP

NEXP is the set of decision problems $L$ for which there is a
polynomial $p$ with natural-number coefficients such that the language of $L$ (the set of
bitstrings on which $L$ is true) belongs to $\mathrm{NTIME}(t)$ for $t(n) = 2^{p(n)}$, where
$\mathrm{NTIME}(t)$ is the class of languages decided by a nondeterministic multi-tape Turing
machine with finitely many states in time $c_1 t(n) + c_2$ for some natural numbers $c_1, c_2$.
