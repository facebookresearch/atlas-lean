# The first pre-phase loop of the wrapped machine

Write $\Gamma'$ for the stack alphabet of
Mathlib's code evaluator. Let $c$ be a code, $a$, $r$, $x$ and $y$ lists of symbols of $\Gamma'$,
$b$ a list of bits of length $k$ and $v$ an internal state (a symbol of $\Gamma'$ or none), and
write $\beta(b)$ for $b$ with each bit $\mathrm{true}$ replaced by the symbol bit1 and each bit
$\mathrm{false}$ by the symbol bit0 of $\Gamma'$. Started at the adapter label pre1 with internal
state $v$, the lists $a$, $r$, $x$ and $y$ on the stacks main, rev, aux and stack, $b$ on the
input stack and the output stack empty, the wrapped machine of $c$ is after exactly $k + 1$ steps
at the adapter label pre2 with internal state none, the reversal of $\beta(b)$ followed by $r$ on
the rev stack, $a$, $x$ and $y$ still on the stacks main, aux and stack, and the input and output
stacks empty.
