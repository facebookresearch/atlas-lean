# Reduction host program

The program of the reduction host for a component with stacks
$c_X$ and $c_O$, an encoding $g_X$ of bits as symbols of $c_X$ and labels $\mathit{start}$ and
$\mathit{done}$. Phase 0 moves the whole input stack onto the buffer $X_1$ with the bit-moving
loop, then moves $X_1$ onto the host's copy of $c_X$ re-encoded by $g_X$ (so in the original
order), then sets the state to false and goes to $\mathit{start}$, or to the cleanup if
$\mathit{start} = \mathit{done}$. At the host label of a component label $l$ it runs the
component's statement at $l$ on the host's copies of the component stacks, with every jump to
$\mathit{done}$ sent to the cleanup. The cleanup pops every stack other than the copy of $c_O$
once per round, repeating while something was popped, and then goes to the final label, which
halts. The phase-0 labels for a separator and a second block halt.
