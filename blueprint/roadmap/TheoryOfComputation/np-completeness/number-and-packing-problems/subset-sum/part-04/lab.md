# Labels of the SUBSET-SUM verifier

The verifier has the labels $\mathrm{tgt}(z)$, reading
the target; $\mathrm{next}$, starting the next number; $\mathrm{add}(c, z)$, adding a chosen
number with carry $c$; $\mathrm{skip}(z)$, skipping an unchosen number; $\mathrm{fin}(c)$,
carrying $c$ through the rest of the sum; $\mathrm{back}$, moving the new sum back;
$\mathrm{fmove}$, moving the final sum for the comparison; $\mathrm{cmp}$, comparing;
$\mathrm{yes}$, accepting; and $\mathrm{no}$, rejecting, for all bits $c$ and $z$. In
$\mathrm{tgt}(z)$, $\mathrm{add}(c, z)$ and $\mathrm{skip}(z)$ the flag $z$ records whether the
bits of the current block read so far end in $0$.
