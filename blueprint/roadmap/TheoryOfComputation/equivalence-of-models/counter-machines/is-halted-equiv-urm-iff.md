# The halting convention is CSLib's

The URM image of a counter state is
halted (`URM.State.isHalted`) for a URM program `q` exactly when the program counter is
past the end of `q`, the counter-machine halting test `prog.length ≤ s.pc` for a
program `prog` of the same length.
