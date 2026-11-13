# The evaluator's encoding of a one-element list

For every natural number $m$, the list of
stack symbols by which Mathlib's code evaluator encodes the one-element list $[m]$ is the binary
encoding of $m$ (least significant bit first) with each bit written as $\mathrm{bit1}$ if it is
true and as $\mathrm{bit0}$ if it is false, followed by the symbol $\mathrm{cons}$.
