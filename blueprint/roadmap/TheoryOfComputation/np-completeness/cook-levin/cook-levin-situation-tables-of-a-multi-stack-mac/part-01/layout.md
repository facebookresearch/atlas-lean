# Clause layout of a machine encoding

For an encoding $E$ of a finite TM2 machine $M$, the
layout of the transition clauses has label/state block size $A = A_0 + N$, where $A_0$ is the
number of label/state codes and $N = A_0 G$ is the number of situations ($G$ the number of
window combinations), together with the number $K$ of numbered stacks, the symbol-code bound $g$
and the window depth $d$ of $M$. The block is a one-hot part on $[0, A_0)$ followed by one
variable per situation.
