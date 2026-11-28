# Consensus repair of the multiplexer trace

Consider the transport-delay experiment for the multiplexer $(a \wedge b) \vee (\neg a \wedge c)$ with both data inputs $b$ and $c$ held true, the select input $a$ rising at time $0$, nonnegative delays $d_1$ and $d_2$ on the positive and complemented paths and $d_{\mathrm{or}}$ on the output gate, and the consensus path $b \wedge c$ initialized true before time $0$. With the consensus path added to the output, the repaired trace is true at every real time, for every choice of the three nonnegative delays.

This concerns that specified experiment only. The repair preserves the Boolean function of the multiplexer; it does not make that function constantly true: with both data inputs false, even the static repaired function is false.
