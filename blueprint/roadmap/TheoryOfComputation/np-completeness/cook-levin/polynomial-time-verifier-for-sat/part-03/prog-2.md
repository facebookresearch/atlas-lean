# The lookup program

The lookup machine works on the stacks $T$, $B$, $S$, $A$, $C$ and
$V$ and acts at each label as follows. At $\mathsf{init}$ it pushes the bit symbol of false onto
$V$ and goes to $\mathsf{scan}$. At $\mathsf{scan}$, if the top of $B$ is a table marker it moves
that marker onto $S$ and goes to $\mathsf{cmp}(b)$ if the marker is $\mathsf{val}(b)$ and to
$\mathsf{mvN}$ if it is $\mathsf{dead}$; if $B$ is empty or has another symbol on top it goes to
$\mathsf{back}$. At $\mathsf{cmp}(b)$ it compares the bit blocks on top of $T$ and $B$: while
both tops are equal bits it pops them, pushes that bit symbol onto $A$ and onto $C$ and stays at
$\mathsf{cmp}(b)$; when both blocks end together it goes to $\mathsf{put}(b)$, and on a mismatch
(different bits, or one block ending first) it goes to $\mathsf{rstT}$ without popping. At
$\mathsf{put}(b)$ it pops $V$, pushes the bit symbol of $b$ onto $V$ and goes to
$\mathsf{rstT}$. At $\mathsf{rstT}$, $\mathsf{rstB}$, $\mathsf{mvN}$ and $\mathsf{back}$ it moves
the bit block on top of $A$ onto $T$, of $C$ onto $B$, of $B$ onto $S$ and of $S$ onto $B$
respectively, staying at the label while the top is a bit and then going to $\mathsf{rstB}$,
$\mathsf{mvN}$, $\mathsf{scan}$ and $\mathsf{mark}$ respectively. At $\mathsf{mark}$, if the top
of $S$ is a table marker it moves that marker onto $B$ and goes to $\mathsf{back}$; if $S$ is
empty or has another symbol on top it goes to $\mathsf{done}$. At $\mathsf{done}$ it halts.
