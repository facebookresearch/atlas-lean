# Relabelling preserves what a machine computes

Let $M$ and $M'$ be deterministic machines
with $k$ work tapes over the same alphabet such that $M'$ simulates $M$ up to a state relabelling
$f$. Then for all words $x$ and $o$ over the alphabet, $M'$ started on input $x$ eventually halts
with output $o$ if and only if $M$ does.
