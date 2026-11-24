# Carry phase of the SUBSET-SUM verifier

Let $x$, $w$, $t$ and $\mathit{acc}$ be lists of
stack symbols, $u$ a list of bits, $c$ a carry bit and $v$ a Boolean, and write
$\mathrm{inc}(c, u)$ for the result of adding the carry $c$ to $u$ (least significant bit first).
Started at label $\mathrm{fin}(c)$ with variable $v$, with $x$, $w$, $t$ on the stacks $X$, $W$,
$T$, the bits of $u$ on $A$ (first bit on top), $\mathit{acc}$ on $B$ and $P$, $Q$ empty, the
verifier takes exactly $|u| + 1$ steps to reach label $\mathrm{back}$ with variable true, where
$X$, $W$, $T$ are unchanged, $A$, $P$, $Q$ are empty, and $B$ holds the bits of
$\mathrm{inc}(c, u)$ on top of $\mathit{acc}$, last bit on top.
