# The readout in polynomial time

A finite multi-stack Turing machine, given the output
encoding $\mathrm{encOut}(o)$ of a result $o$ of the clocked universal function (a list of
symbols, or a timeout), outputs the one-bit list $[\mathrm{diagAnswer}(o)]$ within a number
of steps polynomial in the length of $\mathrm{encOut}(o)$. Here $\mathrm{diagAnswer}(o)$ is
$\mathrm{true}$ unless $o$ is a halt whose output is the single symbol of the bit
$\mathrm{true}$.
