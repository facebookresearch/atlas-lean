# Output phase of the KG-map machine

Let $m$ be a mode, $r$ a list of bits and $n$ and
$c$ natural numbers. Consider a configuration of the KG-map machine $M_m$ at the label output
pair bits, with any internal bit, in which stack $Y$ holds the symbols $\mathrm{val}(b)$ for the
bits $b$ of $r$ in reverse order (the last bit of $r$ on top), stack $B$ holds $n$ copies of the
unit symbol, the counter of $m$ ($A$ for flip, $D$ for vc) holds $c$ copies of some symbol, and
the output stack $O$ is empty. Then in exactly $|r| + n + c + 4$ steps $M_m$ reaches the halting
label with $O$ equal, top first, to the encoding of the instance with numbers $c$ and $n$ and
pair bits $\beta_m(r)$: $c$ trues, a false, $n$ trues, a false, then $\beta_m(r)$, where
$\beta_m$ negates every bit for flip and leaves the bits unchanged for vc.
