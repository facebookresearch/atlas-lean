# The SAT verifier

The SAT verifier takes a pair $(x, w)$ of lists of Booleans, an input
$x$ and a witness $w$, and returns a Boolean together with a declared time cost. If the complete
CNF decoder fails on $x$, it returns false at cost $0$. If $x$ decodes to a CNF formula
$\varphi$, it returns the result and the cost of the CNF check of $\varphi$ against the witness
$w$ and the occurrence list of $\varphi$, so that $w$ is read as values for the variables of
$\varphi$ in order of occurrence.

Decoding the input is uncharged preprocessing: it adds nothing to the declared cost.
