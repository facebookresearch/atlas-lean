# The first post-phase loop of the wrapped machine

Write $\Gamma'$ for the stack alphabet of
Mathlib's code evaluator. Let $c$ be a code, $b$ a list of bits of length $k$, $r$ a list of
symbols of $\Gamma'$, $o$ a list of bits and $v$ an internal state (a symbol of $\Gamma'$ or
none), and write $\beta(b)$ for $b$ with each bit $\mathrm{true}$ replaced by the symbol bit1 and
each bit $\mathrm{false}$ by the symbol bit0 of $\Gamma'$. Started at the adapter label post1
with internal state $v$, $\beta(b)$ followed by the symbol cons on the main stack, $r$ on the rev
stack, $o$ on the output stack and all other stacks empty, the wrapped machine of $c$ is after
exactly $k + 1$ steps at the adapter label post2 with internal state cons, the reversal of
$\beta(b)$ followed by $r$ on the rev stack, $o$ on the output stack and all other stacks
empty.
