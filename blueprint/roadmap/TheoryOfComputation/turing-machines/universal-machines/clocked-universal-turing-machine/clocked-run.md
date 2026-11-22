# The clocked universal machine on stacks

Let $c$ be a code, $x$ a list of bits and $T$ a
natural number, and let $|C|$ be the length of the code stack of $c$. Start the program of the
clocked universal machine at the label $\mathsf{sc0}$, with any value of its internal variable,
on the stacks holding the code $c$, the clock $T$ and the initial configuration on $x$, all other
stacks empty. If the clocked evaluation of $c$ on $x$ for $T$ steps is defined, the machine
reaches the label $\mathsf{hlt}$ on the stacks holding $c$, some clock $t'$ and the configuration
of $c$ after $T$ steps on $x$; otherwise it reaches the label $\mathsf{tmo}$ on the stacks holding
$c$, the clock $0$ and some configuration. In both cases the internal variable ends with some
value, all other stacks are empty, and the run takes at most $(T + 1)(14|C| + 19)$ steps, the
step bound of the clocked machine on the clock $T$.

When the clocked evaluation is defined, its value is the output of the configuration of $c$ after
$T$ steps on $x$.
