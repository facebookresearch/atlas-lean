# The decider within time

Let $M$ be a finite multi-stack machine with finite stack
alphabets, whose input alphabet is identified with the bits by $e$ and whose output alphabet by
$e_1$, and let $C$ be the emulation constant of $M$. Let $w$ be a bit list, $b$ a bit and $t$ a
natural number. Suppose $M$, started with its input stack holding the bits of $w$ in reverse order
followed by $\mathrm{true}$ (read through $e^{-1}$), is after exactly $t$ steps in the halting
configuration whose output stack holds just $e_1^{-1}(b)$, whose other stacks are empty and whose
internal state is the initial one. Then the single-tape decider of $M$, started on the tape of
input-bit cells of $w$, halts on the one-cell tape holding the input-bit cell of $b$ within
$C t (|w| + 1 + C t + 1) + 4$ steps.
