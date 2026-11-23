# The 3-COLOR emitter clears its OR-output counter

Let $m$ be a quiescent state of the
3-COLOR emitter whose OR-output counter $R$ has value $r$, let $v$ be a Boolean and $b$ a Boolean.
Then there is a Boolean $v'$ such that the emitter runs in exactly $r + 1$ steps from label
$\mathsf{clr}(b)$ with internal state $v$ and the stacks of $m$ to the stacks of $m$ with $R$ set
to $0$ and internal state $v'$, at label $\mathsf{fA}(\mathrm{false})$ if $b$ is true and at
label $\mathsf{cls}$ otherwise.
