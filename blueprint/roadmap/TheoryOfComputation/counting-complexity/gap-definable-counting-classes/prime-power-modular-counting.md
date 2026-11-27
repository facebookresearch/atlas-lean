# Mod_{p^k}P = Mod_pP for prime p

For every prime $p$ and $k\ge1$, $\mathsf{Mod}_{p^k}\mathsf{P}=\mathsf{Mod}_p\mathsf{P}$. For a composite $m$ with prime factors $p_1,\dots,p_r$, $\mathsf{Mod}_m\mathsf{P}$ is the class of languages $L_1\cup\dots\cup L_r$ with $L_i\in\mathsf{Mod}_{p_i}\mathsf{P}$.

## Proof sketch

$f\not\equiv0\pmod{p^k}$ iff some $p$-adic digit of $f$ below position $k$ is nonzero; by Lucas' theorem, the $i$-th digit is $\binom{f}{p^i}\bmod p$, and binomial coefficients of $\#\mathsf{P}$ functions are $\#\mathsf{P}$ functions. Combine the $k$ tests by the closure of $\mathsf{Mod}_p\mathsf{P}$ under union (via $1-\prod(1-g_i^{p-1})$).

## Depends on

- [GapP and the gap-definable classes SPP, WPP, LWPP, AWPP, C=P and Mod_kP](gap-definable-classes.md)

## Proof depends on

- [Closure properties of GapP](gapp-closure.md)

## Sources

- Richard Beigel and John Gill, "Counting Classes: Thresholds, Parity, Mods, and Fewness", Theoretical Computer Science 103(1), 1992.
