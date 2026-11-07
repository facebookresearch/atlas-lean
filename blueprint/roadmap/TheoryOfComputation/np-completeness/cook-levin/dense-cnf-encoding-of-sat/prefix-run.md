# Splitting the verifier input

For all bit strings $w$ and $y$, the verifier program
leads in exactly $(|w| + 1) + (|y| + 1) + (|w| + 1) + (|y| + 1)$ steps from the configuration at
label $\mathsf{read1}$ with empty machine state, the input stack holding (from the top) the bits
$b$ of $w$ as $\mathrm{inl}\,b$, the separator $\mathrm{inr}\,\mathrm{none}$ and the bits $b$ of
$y$ as $\mathrm{inr}(\mathrm{some}\,b)$, and all other stacks empty, to the configuration at label
$\mathsf{c0}(\mathrm{false})$ with empty machine state, the input stack holding the bits $b$ of
$w$ as $\mathrm{inl}\,b$, the stack $B$ holding the bits $b$ of $y$ as $\mathrm{inl}\,b$ (both from
the top in order), and the stacks $F$, $A$ and the output stack empty.

The four phases stash $w$ on $F$ and $y$ on $A$, then move them back onto the input stack and
$B$.
