# Regular expressions with squaring: universality is EXPSPACE-complete

The universality
problem for postfix regular expressions with squaring belongs to $\mathsf{EXPSPACE}$, and every
decision problem in $\mathsf{EXPSPACE}$ reduces to it by a polynomial-time many-one reduction.
Here the universality problem accepts a bitstring exactly when it decodes to a list of
natural-number tokens whose postfix evaluation, started on the empty stack, returns the set of
all bitstrings.

## Sources

- A. R. Meyer and L. J. Stockmeyer, "The equivalence problem for regular expressions with squaring requires exponential space", Proceedings of the Thirteenth Annual Symposium on Switching and Automata Theory (1972), 125-129. (The exponential-time word problem in Stockmeyer- Meyer (STOC 1973) is membership, not universality.)
