# Verifying a decision problem with a witness bound

A timed verifier $V$, which assigns to
each pair of bit strings $(x, w)$ (an input and a witness) a timed computation returning a
Boolean, verifies a decision problem $L$ with witness bound $p$, a polynomial with natural
coefficients, when for every bit string $x$, $L(x)$ holds if and only if there is a witness $w$
with $|w| \le p(|x|)$ such that $V(x, w)$ returns true.

This is the verifier half of the definition of NP, phrased for a named timed verifier.
