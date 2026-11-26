# Reading a bit of $x$

The input $x \# w$ of the verifier host is a word over the pair alphabet, which has five symbols:
a left-tagged copy $\overline{b}$ of each bit $b$ (a bit of $x$), a right-tagged copy
$\widehat{b}$ of each bit $b$ (a bit of $w$), and the separator $\#$. The decoder for bits of $x$
is the partial map from the pair alphabet to the bits that is defined exactly at the symbols
$\overline{b}$, where it takes the value $b$; it is undefined at the separator $\#$ and at the
symbols $\widehat{b}$.
