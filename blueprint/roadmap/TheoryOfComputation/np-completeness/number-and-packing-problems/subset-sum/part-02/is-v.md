# Test for the value symbol true (SUBSET-SUM reduction machine)

On the result of a pop,
which is either a symbol or nothing (when the stack was empty), the test returns true exactly when
the result is the value symbol $\mathrm{val}(\mathrm{true})$, which this machine uses for a pair
bit or vertex mark that is true, and false otherwise.
