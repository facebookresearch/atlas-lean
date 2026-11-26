# Program of the readout machine

The readout machine pops the bits of its input stack
$X$ one at a time and compares them with $\mathrm{true}, \mathrm{true}, \mathrm{true},
\mathrm{false}$, which encode, at the output of the clocked universal machine, a halt whose
output is the single symbol of the bit $\mathrm{true}$. If the input is exactly this list, it
pushes $\mathrm{false}$ onto its output stack $O$; otherwise (at the first bit that differs,
when the input ends early, or when a fifth bit follows) it pushes $\mathrm{true}$. Then it
halts.
