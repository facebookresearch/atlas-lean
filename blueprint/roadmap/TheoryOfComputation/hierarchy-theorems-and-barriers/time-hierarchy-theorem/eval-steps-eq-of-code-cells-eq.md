# The code stack determines the clocked semantics

If two codes $c$ and $c'$ have the same code stack (the bit list that encodes them), then their
clocked evaluations agree: for every input $x$ and every step bound $T$, the clocked evaluation of
$c$ on $x$ with bound $T$ (the output if the run has halted within $T$ steps, and no result
otherwise) equals that of $c'$.
