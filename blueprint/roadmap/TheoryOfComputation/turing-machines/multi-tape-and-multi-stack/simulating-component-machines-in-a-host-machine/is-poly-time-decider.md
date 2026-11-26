# Decider host

Let $c$ be a component machine with stacks $c_X$ and $c_O$ and labels
$\mathit{start}$ and $\mathit{done}$, where the statement at $\mathit{done}$ is the halting
statement. Let $g_X$ map bits to symbols of $c_X$, let $e_O$ be a bijection from the alphabet of
$c_O$ to the booleans, let $L$ map bit lists to booleans, and let $p$ be a polynomial with
coefficients in $\mathbb{N}$. Suppose that for every bit list $x$, the component started at
$\mathit{start}$ with internal state false, with $g_X$ applied to each bit of $x$ on $c_X$ and
every other stack empty, reaches the label $\mathit{done}$ in at most $p(|x|)$ steps with exactly
the one symbol $e_O^{-1}(L(x))$ on $c_O$. Then $L$ is polynomial-time computable for the
canonical bitstring encodings, that is, $L$ belongs to the class $\mathrm{P}$ of decision
problems decidable in polynomial time.

The proof applies the reduction host to $x \mapsto [L(x)]$, read with the one-bit encoding of the
booleans.
