# Declared-time many-one reduction by a timed function

Let $L_1$ and $L_2$ be decision
problems and let $f$ be a timed function that maps each list $x$ of Booleans to a list $f(x)$ of
Booleans together with a declared time. Then $f$ is a declared-time many-one reduction from $L_1$
to $L_2$ when $f$ computes in declared polynomial time and $L_1(x) = L_2(f(x))$ for every list $x$
of Booleans.

Because declared times are trusted annotations, this is not a polynomial-time many-one reduction
in the Turing-machine sense: nothing is established about the computability of $f$.
