# Each step of the $\mathrm{TM1}$ emulator is at most three single-tape steps

Let $M$ be
a multi-stack machine with a default label and a default internal state. If the
$\mathrm{TM1}$ emulator of $M$ goes from $c$ to $c'$ in exactly $m$ steps, then the
single-tape emulation of $M$ goes from the single-tape form of $c$ to the single-tape form of
$c'$ in at most $3m$ steps.
