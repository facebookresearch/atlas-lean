# Pushing a list onto a verifier work stack

Given an optional work stack $t$, a list $ys$
of work symbols and work-stack contents $V$ (a list $V(s)$ of symbols for each work stack $s$),
the contents obtained by pushing the elements of $ys$ one at a time onto $t$: if $t$ is a work
stack, $V(t)$ is replaced by the reverse of $ys$ followed by $V(t)$ and every other stack is
unchanged; if $t$ is none, the result is $V$.
