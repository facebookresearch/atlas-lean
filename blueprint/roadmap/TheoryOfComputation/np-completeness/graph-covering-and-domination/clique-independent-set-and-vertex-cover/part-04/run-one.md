# One step of a clique-verifier program to a known label

Let $M$ be a program that
assigns a verifier statement to each label, $\ell$ and $\ell'$ labels, $v$ a state and $S$
stack contents. If executing the statement $M(\ell)$ from state $v$ and stacks $S$ ends at
label $\ell'$, then there are a state $v'$ and stack contents $S'$ such that $M$ runs in
exactly one step from label $\ell$ with state $v$ and stacks $S$ to label $\ell'$ with
state $v'$ and stacks $S'$.
