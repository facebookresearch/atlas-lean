# Parity in depth two with n + 1 threshold gates

Every symmetric Boolean function of $n$ bits has a threshold circuit of depth two and $O(n)$ gates. For parity: with $g_j=\mathrm{Th}^n_{\ge j+1}$ for $0\le j<n$, the depth-two circuit $\mathrm{Th}_{\ge\lfloor n/2\rfloor+1}\bigl(g_0,\neg g_1,g_2,\neg g_3,\dots\bigr)$ computes $x_1\oplus\cdots\oplus x_n$; it has $n+1$ threshold gates and $\lfloor n/2\rfloor$ negations.

## Proof sketch

If $w$ inputs are true then $g_j=1$ iff $j<w$; after negating the odd-indexed $g_j$, exactly $\lfloor n/2\rfloor+(w\bmod 2)$ of the $n$ signed values are true, so the top gate reads off the parity of $w$.

## Depends on

- [Threshold gates and the basis of threshold circuits](threshold-gates-and-threshold-circuits.md)
- [The parity language](../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)

## Sources

- András Hajnal, Wolfgang Maass, Pavel Pudlák et al., "Threshold Circuits of Bounded Depth", Journal of Computer and System Sciences, 1993.
