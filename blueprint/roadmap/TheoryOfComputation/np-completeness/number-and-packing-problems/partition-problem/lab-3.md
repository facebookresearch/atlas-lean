# Control labels of the SUBSET-SUM to PARTITION padding machine

The labels of the padding machine are $\mathsf{target}$ (read the target), $\mathsf{copy}$ and
$\mathsf{distribute}$ (keep the numbers and hand them to the summation machine), a copy of each
label of the SUBSET-SUM summation machine, then $\mathsf{targetStart}$, $\mathsf{targetBits}$
(write the block of twice the target), $\mathsf{prefix}$, $\mathsf{bits}$ (write the block of the
sum) and $\mathsf{done}$.
