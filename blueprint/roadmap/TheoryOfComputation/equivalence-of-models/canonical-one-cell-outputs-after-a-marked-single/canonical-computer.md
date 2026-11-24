# Canonical Computer

Assume that `Γ` is finite and that `Γ` is inhabited (it has a designated default element).

Simulate `tm` with visited-cell markers, then erase both halves and return to its answer head.
The source transition is followed by one stationary normalization step, including when it halts.
No cleanup state is reachable from the simulation unless the source enters its halting state.
