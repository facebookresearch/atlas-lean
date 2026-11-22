# The emulation halts where the multi-stack machine halts

Let $M$ be a multi-stack machine with a default label and a default internal state, let $c$ be a
configuration of $M$, and let $c_1$ be a configuration of the $\mathrm{TM1}$ emulator of $M$ that
corresponds to $c$ under the simulation relation. If $M$ has no step from $c$, then the single-tape
emulation of $M$ has no step from the single-tape form of $c_1$.
