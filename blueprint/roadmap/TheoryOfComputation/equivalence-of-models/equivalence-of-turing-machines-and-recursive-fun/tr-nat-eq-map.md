# The evaluator encodes numbers in binary

For every natural number $n$, the list of stack
symbols by which Mathlib's code evaluator encodes $n$ is obtained from the binary encoding of $n$
(least significant bit first) by writing each bit as $\mathrm{bit1}$ if it is true and as
$\mathrm{bit0}$ if it is false.
