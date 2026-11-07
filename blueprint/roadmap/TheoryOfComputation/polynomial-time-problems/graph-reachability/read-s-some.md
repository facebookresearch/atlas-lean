# Reading a unary number

Let $d$ be a stack other than $X$, let $g$ encode bits as symbols
of $d$, and let $ps$ be a list of stack–symbol pairs whose stacks are distinct and differ from $X$
and $d$. Suppose the instruction of the marking machine at a label $\ell$ is the unary read off
$X$ onto $d$ through $g$ that pushes $ps$ for each true bit, repeats at $\ell$ and continues at
$\ell'$. If $X$ holds, as bit symbols, $k$ true bits, then a false bit, then a bit list $r$, then
in exactly $k + 1$ steps the machine goes from $\ell$, with any flag, to $\ell'$; afterwards $X$
holds $r$, $d$ has received $k$ copies of $g(\mathrm{true})$ and then $g(\mathrm{false})$ on top,
each stack $q$ with a pair $(q, a)$ in $ps$ has received $k$ copies of $a$ on top, and every
other stack is unchanged.
