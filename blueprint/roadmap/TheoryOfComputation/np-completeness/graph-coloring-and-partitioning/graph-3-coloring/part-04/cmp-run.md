# Name comparison in the 3-COLOR emitter

Let $m$ be a quiescent state, $u$ and $w$ lists
of bits, and $R$ a list of symbols that is empty or does not start with a name bit. If stack $A$
of $m$ holds $u$ as name bits and stack $D$ holds $w$ as name bits followed by $R$, then from
label $\mathsf{cmp}$ with the stacks of $m$ and any flag, the emitter reaches, in at most
$3|w| + 3$ steps, label $\mathsf{sel}$ if $u = w$ and label $\mathsf{mvN}(\mathrm{none})$
otherwise, with the stacks of $m$ restored and some flag.
