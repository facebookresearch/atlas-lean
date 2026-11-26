# Applying an effect to the original stacks

Let $S_0$ assign a list $S_0(k)$ to each stack
$k$, and let $r = (\ell, v, P, c)$ consist of a label $\ell$ (possibly the halted label), a state
$v$, a list $P(k)$ for each stack $k$ and a natural number $c(k)$ for each stack $k$. This is the
configuration with label $\ell$, state $v$, and stack $k$ equal to $P(k)$ followed by $S_0(k)$
with its first $c(k)$ symbols (from the top) removed.

Applied to an effect, $P(k)$ is the pushed prefix still on top of stack $k$ and $c(k)$ is the net
number of original symbols consumed.
