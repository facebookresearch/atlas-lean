# The start word

For an input $l$ of tape symbols, the start word is
$\vdash q_0\, h\, R \dashv$, where $\vdash$ and $\dashv$ are the left and right end markers,
$q_0$ is the default state, $h$ is the first symbol of $l$ (the default tape symbol if $l$ is
empty) and $R$ is the rest of $l$. It spells the configuration in state $q_0$ with head symbol
$h$, empty left part and right part $R$.
