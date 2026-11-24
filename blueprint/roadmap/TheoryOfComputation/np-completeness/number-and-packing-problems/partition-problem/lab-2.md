# Control labels of the raw-input SUBSET-SUM to PARTITION machine

The labels of the raw-input machine are $\mathsf{copy1}$ and $\mathsf{copy2}$ (duplicate the
input), a copy of each label of the [list normalizer](../../cook-levin/conversions-between-bit-string-encodings/a-finite-list-nat-canonicalizer/README.md), $\mathsf{nonempty}$ and
$\mathsf{compare}$ (check that the input is a canonical encoding), $\mathsf{restore}$ and
$\mathsf{start}$ (hand it to the padding machine), a copy of each
[label of the padding machine](lab-3.md), then $\mathsf{bad}$ and $\mathsf{done}$.
