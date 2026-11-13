# Decrement

For a stack $k$ and labels $\ell_0$ and $\ell_+$, this machine statement pops
stack $k$, stores in the state whether a symbol was popped, and goes to $\ell_+$ if a symbol was
popped and to $\ell_0$ if stack $k$ was empty.
