# Program of the canonical PARTITION membership transducer

The program of the membership transducer, on its [stacks](k-5.md) and [labels](lab-5.md), with
Boolean internal state. At $\mathsf{copy}$ it moves the bits of $X$ onto $R$ one at a time, then
goes to $\mathsf{distribute}$. At $\mathsf{distribute}$, if $R$ is empty it goes to the summation
machine's label $\mathsf{next}$; otherwise it pops a bit $b$ of $R$, pushes $b$ onto the summation
machine's input stack (as a bit symbol) and onto the doubling machine's input stack, pushes a true
witness bit onto the summation machine's witness stack, and repeats. At the copy of a label of the
summation machine it runs that machine's instruction on its copied stacks, with labels renamed by
the [label map](sum-label-2.md); at the copy of a label of the doubling machine it runs the
[doubling machine](prog.md)'s instruction on its copied stacks, with labels renamed by the
[label map](double-label.md). At $\mathsf{prefix}$ it pushes false onto the doubling machine's
output stack $O$ and goes to $\mathsf{bits}$. At $\mathsf{bits}$, while the summation machine's
stack $B$ is nonempty it pops its top symbol, read as a bit $b$ (false if it is not a bit), and
pushes $b$, then true, onto $O$; once $B$ is empty it goes to $\mathsf{done}$, where it halts.
