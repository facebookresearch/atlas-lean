# The emulator walks right to the top of a stack

Let $M$ be a multi-stack machine, $k$ a
stack, $L$ tape contents whose $k$-th track lists a stack $S$ from bottom to top, and
$n \le |S|$. In the $\mathrm{TM1}$ emulator of $M$, the configuration in the state that walks to
stack $k$ (for a given stack action and continuation), with internal state $v$ and head at the
bottom marker of $L$, reaches in exactly $n$ steps the same configuration with the head moved
$n$ cells to the right.
