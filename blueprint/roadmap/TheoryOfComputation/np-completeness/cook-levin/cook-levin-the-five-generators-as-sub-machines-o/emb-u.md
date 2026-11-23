# Embedding of the update generator's stacks into the host

For $g \in \mathbb{N}$, this is
the stack embedding of the family generator's stacks (a Boolean output stack and one unit counter
stack per counter) into the host stacks with $g$ input codes, used for the update generator: the
output stack goes to the host's shared output stack, and the counter stack $x$ goes to the stack
$x$ of the host's private update block. Distinct stacks go to distinct host stacks, and each
stack's alphabet is identified with its host stack's alphabet by the identity.
