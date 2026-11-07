# Effect of the mark-setting step

Let $\ell$ be a label, $v$ an internal state and $S$
stacks whose mark stack $M$ holds the bits of a list $l$ of booleans. Executing the mark-setting
step to $\ell$ from internal state $v$ and stacks $S$ ends at label $\ell$ with some internal
state and the stacks $S$ with $M$ replaced by the bits of $l$ with its first entry set to true
(the empty list stays empty); every other stack is unchanged.
