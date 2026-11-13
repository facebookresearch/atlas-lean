# Reading a cut-off unary number

Let $d$ be a stack other than $X$ and $O$, let $g$ encode
bits as symbols of $d$, and let $ps$ be a list of stack–symbol pairs whose stacks are distinct and
differ from $X$ and $O$. Suppose the instruction of the marking machine at a label $\ell$ is the
unary read off $X$ onto $d$ through $g$ that pushes $ps$ for each true bit, repeats at $\ell$ and
continues at $\ell'$. If a bit list $l$ has no unary length prefix (every bit of $l$ is true) and
$X$ holds $l$ as bit symbols, then from $\ell$, with any flag, the machine reaches the label `bad`
within $|l| + 1$ steps, leaving the output stack $O$ unchanged.
