# The reduction host's run on one input

Let $c$ be a component with stacks $c_X$ and $c_O$,
an encoding $g_X$ of bits as symbols of $c_X$, an identification $e_O$ of the alphabet of $c_O$
with the bits, and labels $\mathit{start}$ and $\mathit{done}$, where the component halts at
$\mathit{done}$. Let $p$ be a polynomial with natural-number coefficients and $x$, $o$ bit lists,
and suppose that the component, started at $\mathit{start}$ with state false, with $x$ encoded by
$g_X$ on $c_X$ and every other stack empty, reaches $\mathit{done}$ within $p(|x|)$ steps with
some state and stacks in which $c_O$ holds $o$ translated symbol by symbol by $e_O^{-1}$. Then the
reduction host program, started at its first phase-0 label with state false, $x$ on the input
stack and every other stack empty, halts within $T(|x|)$ steps, where $T$ is the reduction host's
step bound for $p$, with state false, $o$ translated by $e_O^{-1}$ on the host's copy of $c_O$ and
every other stack empty.
