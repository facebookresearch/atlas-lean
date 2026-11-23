# Reading one pair of a block

For a flag $z$ (the bits read so far end in false), a
statement $\mathit{done}$ and statements $\mathit{body}(b)$ for each bit $b$: if the input stack
$X$ is empty, go to the label $\mathsf{no}$. Otherwise pop the top of $X$ as a bit, a symbol that
is not a bit counting as false. If it is false (the end marker), go to $\mathsf{no}$ when $z$ is
true and run $\mathit{done}$ otherwise. If it is true, go to $\mathsf{no}$ if $X$ is now empty,
and otherwise pop the next symbol of $X$ as a payload bit $b$ (again a non-bit counts as false)
and run $\mathit{body}(b)$.
