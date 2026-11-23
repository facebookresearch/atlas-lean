# Binary addition program built on the SUBSET-SUM machine

The program of the binary addition machine, on the seven stacks of the SUBSET-SUM verifier, with
the [labels](lab.md) of the verifier and the labels $0, 1, 2, 3$, and Boolean internal state. At
label $0$ it pushes two true bit symbols onto the witness stack $W$ and goes to the verifier's
label $\mathsf{next}$. At a verifier label it runs the instruction of the [SUBSET-SUM verifier program](../part-05/prog.md) with
the halting labels $\mathsf{yes}$ and $\mathsf{no}$ [redirected](redirect.md) to $1$. At label
$1$ it pops the top of $W$, repeating while $W$ was nonempty, and then goes to $2$. At label $2$
it moves the bit symbols of the stack $B$ onto the stack $A$ one at a time, then goes to $3$. At
label $3$ it halts.
