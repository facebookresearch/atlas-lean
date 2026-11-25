# Inversion success probability of a circuit

Let $f$ map $n$-bit strings to bitstrings
and let $C$ be an encoded flat Boolean circuit. For an $n$-bit string $x$, the candidate preimage
$x'$ consists of the last $n$ gate values of $C$ on input $f(x)$ (all of them if $C$ has fewer
than $n$ gates), padded with false to length $n$. The inversion success probability of $C$
against $f$ is the fraction of the $2^n$ strings $x$ for which $f(x') = f(x)$.
