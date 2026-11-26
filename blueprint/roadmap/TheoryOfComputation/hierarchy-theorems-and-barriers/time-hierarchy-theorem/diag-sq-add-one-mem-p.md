# The quadratic diagonal language is in P

The diagonal language for the time bound
$f(n) = n^2 + 1$, the set of bit lists $x$ that encode a code which does not halt on $x$ within
$|x|^2 + 1$ steps with the answer $\mathrm{true}$, is in the class P of decision problems
decidable in polynomial time.

The decider decodes the canonical encoding of bit lists and then runs a polynomial-time decider
on the raw bits.
