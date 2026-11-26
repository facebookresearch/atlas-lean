# Every decision problem has a timed decider in declared polynomial time

For every decision
problem $L$ there is a timed function $f$ from lists of Booleans to Booleans that decides in
declared polynomial time and whose output $f(x)$ equals $L(x)$ for every list $x$ of Booleans.

The witness returns $L(x)$ with declared time $0$, treating the evaluation of $L$ as free. This is
why no complexity classes are defined by quantifying over timed functions.
