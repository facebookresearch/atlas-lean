# The assembled generator, after the precomputation

Let $E$ be an encoding of a machine
$M$, let $x$ and $Y$ be lists of input symbols of $M$, let $a$ be a symbol of its output stack,
and let $m, T \in \mathbb{N}$ with $|x| \le m$. Put $H = m + (T + 1)d + 1$, where $d$ is the
window depth of $M$. Let $S_0$ be host stacks whose output stack holds a word $o$, whose input
stack holds the symbol codes of $x$ in reverse order, whose update, situation-definition, shift
and accept blocks each hold $T$ on the time counter, $H$ on the height counter and nothing on the
other counters, and whose init block holds $T$, $|x|$, $m - |x|$ and $H - m$ on its four size
counters and nothing on the others. Then the host program on the real generators of $E$ for $Y$
and $a$, started at the init generator's start label with state bit false on $S_0$, reaches its
final label within the step bound $\mathrm{realB}(E, Y, m, T)$ (the five generators' bounds plus
five chaining steps), with some state bit and with output stack the dense encoding of the formula
$\Phi(E, x, Y, a, m, T)$ followed by $o$.
