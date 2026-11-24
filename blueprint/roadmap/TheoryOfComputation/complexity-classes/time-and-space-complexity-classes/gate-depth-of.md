# Depth of a gate

Let $d$ be the list of depths of the earlier gates of a flat Boolean
circuit on $n$ inputs, and for a gate index $a$ let $d_a$ be the entry of $d$ at (zero-based)
position $a$, or $0$ when $a$ is not a position of $d$. The depth of an input-variable gate or a
constant gate is $0$; the depth of a negation, AND, OR or modular gate is one more than the
maximum of $d_a$ over the gates $a$ it references, where the maximum over no gates is $0$.
