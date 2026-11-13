# Host labels as a sum type

Write $P_0$ for the phase-0 labels, $\Lambda_T$ for the
tokenizer labels, $\Lambda_F$ for the labels of the clause-length filter, and $\Lambda_D$ and
$\Lambda_L$ for the labels of the clause-check driver and of the lookup. The host labels are in
bijection with $P_0 \sqcup \Lambda_T \sqcup \Lambda_F \sqcup (\Lambda_D \sqcup \Lambda_L) \sqcup
\mathrm{Bool} \sqcup \mathrm{Bool}$: a phase-0 label $p$, tokenizer label, filter label, or driver
or lookup label goes to itself in its summand, a cleanup label with answer $a$ goes to $a$ in the
first copy of $\mathrm{Bool}$, and a final label with answer $a$ goes to $a$ in the second copy.
The bijection gives the host labels their finiteness instance.
