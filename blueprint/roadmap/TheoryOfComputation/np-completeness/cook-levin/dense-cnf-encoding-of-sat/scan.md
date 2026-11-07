# The verifier's main scan

For all bit strings $r$, $bs$, $as$, every flag $fl$ and every
machine state $v$, the verifier program leads in exactly $T(r, bs, as, fl)$ steps from the
configuration at label $\mathsf{c0}(fl)$ with machine state $v$, the input stack holding the bits
of $r$, the stack $A$ holding the bits of $as$ and the stack $B$ holding the bits of $bs$ (each bit
$b$ stored as $\mathrm{inl}\,b$, from the top in order), and the stack $F$ and the output stack
empty, to the configuration at label $\mathsf{finish}(\operatorname{evalCNF}(r, bs, as, fl))$
with empty machine state and all stacks empty.
