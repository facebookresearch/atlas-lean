# The drain program

Given a list $k_0, \dots, k_{m-1}$ of stacks, a type $\Lambda$ of
labels and labels $\lambda : \mathbb{N} \to \Lambda$, stage $i$ of the drain program is as
follows. For $i < m$ it pops stack $k_i$, recording in the state whether a symbol was popped, and
jumps to $\lambda(i)$ if one was and to $\lambda(i + 1)$ if the stack was empty; repeated, this
empties $k_i$. For $i \ge m$ it sets the state to store the flag bit false and halts.
