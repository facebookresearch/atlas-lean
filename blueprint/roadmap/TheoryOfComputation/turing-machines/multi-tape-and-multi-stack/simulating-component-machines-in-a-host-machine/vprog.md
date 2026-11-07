# Verifier host program

The program of the verifier host for a component machine $c$ with
stacks $c_X$ and $c_W$, encodings $g_X$ and $g_W$ of bits as symbols of $c_X$ and $c_W$, and
labels $\mathit{start}$, $\mathit{yes}$ and $\mathit{no}$, on the host stacks with the work
alphabet of the dense-SAT verifier on the input stack. On an input $x \# w$ in the pair encoding,
phase 0 moves the symbols on top of the input stack that encode bits of $x$ onto the buffer $X_1$
with the bit-moving loop, then moves $X_1$ onto the host's copy of $c_X$ re-encoded by $g_X$ (so
in the original order); it pops one symbol off the input stack (the separator $\#$); it moves
the symbols that encode bits of $w$ onto the buffer $W_1$ and then $W_1$ onto the host's copy of
$c_W$ re-encoded by $g_W$; then it sets the state to false and goes to the renamed label of
$\mathit{start}$. Here a label of $c$ is renamed to the cleanup label with answer true if it is
$\mathit{yes}$, to the cleanup label with answer false if it is $\mathit{no}$ but not
$\mathit{yes}$, and to the host's copy of itself otherwise. At the host's copy of a component
label $l$ it runs the component's statement at $l$ on the host's copies of the component stacks,
with every jump target renamed. The cleanup label with answer $a$ pops every stack other than the
output stack once per round, repeating while something was popped, and then goes to the output
label with answer $a$, which pushes $a$ on the output stack and halts.
