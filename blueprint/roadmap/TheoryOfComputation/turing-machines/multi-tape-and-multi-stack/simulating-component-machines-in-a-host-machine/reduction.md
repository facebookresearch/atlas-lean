# Reduction host

Let $c$ be a component with stacks $c_X$ and $c_O$, an encoding $g_X$ of
bits as symbols of $c_X$, an identification $e_O$ of the alphabet of $c_O$ with the bits, and
labels $\mathit{start}$ and $\mathit{done}$, where the component halts at $\mathit{done}$. Let $f$
be a function from bit lists to bit lists and $p$ a polynomial with natural-number coefficients.
Suppose that for every bit list $x$ the component, started at $\mathit{start}$ with state false,
with $x$ encoded by $g_X$ on $c_X$ and every other stack empty, reaches $\mathit{done}$ within
$p(|x|)$ steps with some state and stacks in which $c_O$ holds $f(x)$ translated symbol by symbol
by $e_O^{-1}$. Then $f$ is computable in polynomial time on raw bit lists (the identity as input
and output encoding): by the reduction host machine, with the bits as input alphabet, $e_O$ as
output alphabet and the reduction host's step bound for $p$ as time bound.
