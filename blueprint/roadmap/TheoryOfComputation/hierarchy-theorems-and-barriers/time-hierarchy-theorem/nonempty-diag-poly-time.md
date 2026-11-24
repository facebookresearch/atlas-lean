# The diagonal language in polynomial time, given the reformatting machine

Let
$f : \mathbb{N} \to \mathbb{N}$. Suppose that a finite multi-stack Turing machine, the
reformatting machine, computes in polynomial time, from a bit list $x$ given as itself, the
input $\mathrm{encIn}(c, y, T)$ of the clocked universal machine, where
$(c, y, T) = \mathrm{diagArg}_f(x)$ is the argument of the clocked universal function for the
diagonal language $\mathrm{diag}_f$ on $x$. Then a finite multi-stack Turing machine computes
$\mathrm{diag}_f$ in polynomial time: on every bit list $x$, given as itself, it outputs the
one-bit list $[\mathrm{diag}_f(x)]$.

The machine runs the reformatting machine, then the clocked universal machine, then the
readout machine.
