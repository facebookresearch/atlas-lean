# Parity in depth two with n + 1 threshold gates

Let $g_j=\mathrm{Th}^n_{\ge j+1}$ for $0\le j<n$, so that $g_j(x)=1$ iff $j<|x|$. Every symmetric Boolean function $f$ of $n$ bits, written as $f(x)=F(|x|)$, is computed by a depth-two circuit of $n+1$ threshold gates in which only the output gate is weighted:

$$f(x)=\Big[\sum_{j=0}^{n-1}\big(F(j+1)-F(j)\big)\,g_j(x)\ \ge\ 1-F(0)\Big],$$

with weights in $\{-1,0,1\}$. For parity the weights alternate, $+1,-1,+1,\dots$, and the cutoff is $1$:

$$x_1\oplus\cdots\oplus x_n=\Big[\sum_{j=0}^{n-1}(-1)^j g_j(x)\ \ge 1\Big].$$

With unweighted threshold gates and negation only, as in the basis of the linked page, the circuit $\mathrm{Th}_{\ge\lfloor n/2\rfloor+1}\bigl(g_0,\neg g_1,g_2,\neg g_3,\dots\bigr)$ also computes parity with $n+1$ threshold gates and $\lfloor n/2\rfloor$ negations; there a path through $g_1$, its negation and the output gate has length three (already for $n=2$), so its depth is three, or two if negations are not counted.

## Proof sketch

If $w=|x|$ then $g_j=1$ exactly for $j<w$, so the weighted sum telescopes to $F(w)-F(0)$, which is at least $1-F(0)$ iff $F(w)=1$; for parity it is $w\bmod2$. In the unweighted circuit, after negating the odd-indexed $g_j$, exactly $\lfloor n/2\rfloor+(w\bmod 2)$ of the $n$ signed values are true, so the top gate reads off the parity of $w$.

## Depends on

- [Threshold gates and the basis of threshold circuits](threshold-gates-and-threshold-circuits.md)
- [The parity language](../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)

## Sources

- András Hajnal, Wolfgang Maass, Pavel Pudlák et al., "Threshold Circuits of Bounded Depth", Journal of Computer and System Sciences, 1993.
