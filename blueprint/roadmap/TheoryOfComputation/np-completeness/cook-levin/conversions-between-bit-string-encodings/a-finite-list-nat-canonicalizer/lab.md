# Control labels of the list-of-naturals canonicalizer

The labels of the list canonicalizer are loop, block, back, a label $\mathrm{nat}(\ell)$ for each label $\ell$ of
the [payload normalizer machine](../a-linear-time-machine-for-total-binary-payload-n/lab.md), emit, finish, good
and bad. When the normalizer would halt, the canonicalizer continues at emit, which writes the frame of the
normalized number.
