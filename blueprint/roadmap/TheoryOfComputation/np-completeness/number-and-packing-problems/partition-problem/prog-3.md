# Program of the SUBSET-SUM to PARTITION padding machine

The program of the padding machine, on its [stacks](k-3.md) and [labels](lab-3.md), with Boolean
internal state. At $\mathsf{target}$ it pops a bit of $X$ (an empty $X$ reads as false); if it is
true, it pops the next bit, pushes it onto $T$ and repeats, and if it is false it goes to
$\mathsf{copy}$. At $\mathsf{copy}$ it moves the bits of $X$ onto $R$ one at a time, then goes to
$\mathsf{distribute}$. At $\mathsf{distribute}$, if $R$ is empty it goes to the summation
machine's label $\mathsf{next}$; otherwise it pops a bit $b$ of $R$, pushes $b$ onto the
summation machine's input stack (as a bit symbol) and onto $O$, pushes a true witness bit onto
the summation machine's witness stack, and repeats. At the copy of a label of the summation
machine it runs that machine's instruction on the copies of its stacks, with labels renamed by
the [label map](sum-label.md). At $\mathsf{targetStart}$ it pushes false onto $O$ and goes to
$\mathsf{prefix}$ if $T$ is empty, to $\mathsf{targetBits}$ otherwise. At $\mathsf{targetBits}$,
while $T$ is nonempty it pops a bit $b$ of $T$ and pushes $b$, then true, onto $O$; once $T$ is
empty it pushes false, then true, onto $O$ and goes to $\mathsf{prefix}$. At $\mathsf{prefix}$
it pushes false onto $O$ and goes to $\mathsf{bits}$. At $\mathsf{bits}$, while the summation
machine's stack $B$ is nonempty it pops its top symbol, read as a bit $b$ (false if it is not a
bit), and pushes $b$, then true, onto $O$; once $B$ is empty it goes to $\mathsf{done}$, where it
halts.
