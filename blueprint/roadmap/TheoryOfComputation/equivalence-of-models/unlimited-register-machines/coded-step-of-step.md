# A machine step is a coded step

Let $p$ be a URM program, let $R$ be the sum over the
instructions of $p$ of the largest register index each one mentions, and let $s'$ be a state
that $p$ reaches from the state $s$ in one step. Then the coded step, run on the list of codes of
the instructions of $p$, sends the coded state of $s$ (its program counter together with the list
of the contents of its registers $0, \dots, R$) to the coded state of $s'$.
