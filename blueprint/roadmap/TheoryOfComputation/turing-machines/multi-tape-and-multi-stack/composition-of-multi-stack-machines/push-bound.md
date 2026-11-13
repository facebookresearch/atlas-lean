# Push bound of a finite multi-stack Turing machine

For a finite multi-stack Turing
machine $M$ (Mathlib's TM2 model with finitely many labels), the push bound of $M$ is the sum,
over all labels $l$ of $M$, of the number of push instructions in the statement that $M$
assigns to $l$.

No stack of $M$ grows by more than the push bound in a single step.
