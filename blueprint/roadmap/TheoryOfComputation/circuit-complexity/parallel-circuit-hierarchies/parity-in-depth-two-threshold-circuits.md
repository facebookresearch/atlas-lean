# Parity in depth-two threshold circuits of linear size

Every symmetric Boolean function of $n$ bits, in particular parity $x_1\oplus\cdots\oplus x_n$, is computed by a depth-two threshold circuit of linear size and weight $1$: its gates are weighted threshold gates whose weights all have absolute value at most $1$, reading the input literals $x_1,\dots,x_n,\neg x_1,\dots,\neg x_n$ and the constants.

## Proof sketch

Write $f(x)=F(|x|)$ and let $S=\{s_1<\dots<s_k\}$ be the set of weights $|x|$ with $F(|x|)=1$. Feed the $2k$ gate values $\mathrm{Th}_{\ge s_i}(x)$ and $\mathrm{Th}_{\le s_i}(x)$, $i=1,\dots,k$, into a top gate testing whether at least $k+1$ of them are $1$: exactly $k$ of them are $1$ when $|x|\notin S$ and $k+1$ when $|x|\in S$.

Derived here with an exact gate count: let $g_j=\mathrm{Th}^n_{\ge j+1}$ for $0\le j<n$, so that $g_j(x)=1$ iff $j<|x|$. Then

$$f(x)=\Big[\sum_{j=0}^{n-1}\big(F(j+1)-F(j)\big)\,g_j(x)\ \ge\ 1-F(0)\Big],$$

a depth-two circuit of $n+1$ threshold gates in which only the output gate is weighted, with weights in $\{-1,0,1\}$: if $w=|x|$ the sum telescopes to $F(w)-F(0)$. For parity the weights alternate, $+1,-1,+1,\dots$, and the cutoff is $1$:

$$x_1\oplus\cdots\oplus x_n=\Big[\sum_{j=0}^{n-1}(-1)^j g_j(x)\ \ge 1\Big].$$

With unweighted threshold gates and negation only, the circuit $\mathrm{Th}_{\ge\lfloor n/2\rfloor+1}\bigl(g_0,\neg g_1,g_2,\neg g_3,\dots\bigr)$ computes parity with $n+1$ threshold gates and $\lfloor n/2\rfloor$ negations, since exactly $\lfloor n/2\rfloor+(w\bmod 2)$ of the $n$ signed values are true; there a path through $g_1$, its negation and the output gate has length three (already for $n=2$), so its depth is three, or two if negations are not counted.

## Depends on

- [Threshold gates and the basis of threshold circuits](threshold-gates-and-threshold-circuits.md)
- [The parity language](../../complexity-classes/time-and-space-complexity-classes/parity-dec.md)

## Sources

- András Hajnal, Wolfgang Maass, Pavel Pudlák, Mario Szegedy and György Turán, "Threshold Circuits of Bounded Depth", Journal of Computer and System Sciences 46(2), 129–154, 1993 (Section 2, Proposition 2.1 and its proof).
