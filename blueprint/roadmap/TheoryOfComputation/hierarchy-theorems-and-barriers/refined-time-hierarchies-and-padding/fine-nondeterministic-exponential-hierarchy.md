# Fine nondeterministic exponential-time hierarchy by lazy diagonalization

On binary words, for all reals $\delta>0$ and $c_0>0$,

$$
\mathsf{NTIME}\bigl(\lfloor 2^{\,n-c_0 n^{\delta}}\rfloor\bigr)\subsetneq\mathsf{NTIME}(2^{n}),
$$

and $\mathsf{NTIME}(\lfloor 2^{n}/(n+1)^{k}\rfloor)\subsetneq\mathsf{NTIME}(2^{n})$ for every integer $k\ge1$.

## Proof sketch

Both separations are instances of the nondeterministic time hierarchy theorem of Seiferas–Fischer–Meyer and Žák: if $f$ and $g$ are time-constructible and $f(n+1)=o(g(n))$ then $\mathsf{NTIME}(f)\subsetneq\mathsf{NTIME}(g)$ (Arora–Barak Theorem 3.3). Here $g(n)=2^{n}$; when $f$ is not time-constructible (irrational $\delta$ or $c_0$), replace it by the larger time-constructible bound $2^{\,n-\lfloor n^{\delta'}\rfloor}$ for a rational $0<\delta'<\delta$, which satisfies the same hypothesis. Moreover $f(n+1)\le 2^{\,n+1-c_0(n+1)^{\delta}}=o(2^{n})$ because $c_0(n+1)^{\delta}\to\infty$, respectively $f(n+1)\le 2^{n+1}/(n+2)^{k}=o(2^{n})$ for $k\ge1$. The theorem is proved by lazy diagonalization: on an interval of input lengths, mirror the diagonalized machine on the next length until the end of the interval, where the deterministic exponential simulation of the first length is affordable and is used to disagree. The linked hierarchy page is the special case $n$ versus $n^2$.

## Depends on

- [Nondeterministic time classes](../../complexity-classes/time-and-space-complexity-classes/ntime.md)

## Proof depends on

- [Nondeterministic time hierarchy](../nondet-time-hierarchy.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009, Section 3.3 (Theorem 3.3 in the 2007 web draft).
- Stanislav Žák, "A Turing Machine Time Hierarchy", Theoretical Computer Science 26(3), 327–333, 1983.
- Joel I. Seiferas, Michael J. Fischer and Albert R. Meyer, "Separating Nondeterministic Time Complexity Classes", Journal of the ACM 25(1), 146–167, 1978.
