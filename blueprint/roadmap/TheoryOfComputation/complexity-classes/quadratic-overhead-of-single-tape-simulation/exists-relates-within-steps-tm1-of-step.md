# One multi-stack step costs at most $1 + B(2(H + B) + 2)$ emulator steps

Let $M$ be a
multi-stack machine in which the statement of every label has size at most $B$, and consider its
emulation by a single-tape machine with an internal store that keeps the stacks side by side on
its tape. Let $c$ be a configuration of $M$ in which every stack has height at most $H$, and let
$c_1$ be a configuration of the emulator that represents $c$. If $M$ moves from $c$ to $c'$ in one
step, then there is a configuration $c_1'$ of the emulator that represents $c'$ and that the
emulator reaches from $c_1$ in at most $1 + B(2(H + B) + 2)$ steps.

The size of a statement is its structural size as a term. This is a counted form of the
correctness of the emulation.
