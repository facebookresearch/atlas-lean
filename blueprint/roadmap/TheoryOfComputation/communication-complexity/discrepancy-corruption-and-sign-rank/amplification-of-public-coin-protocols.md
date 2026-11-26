# Amplification of public-coin protocols by majority

Let a public-coin protocol of cost $c$ compute a Boolean function with error $\varepsilon \le 1/2$ on every input. Running it $2r$ times with independent coins and answering with the strict majority yields a public-coin protocol of cost $2rc$ with error at most $(4\varepsilon(1 - \varepsilon))^r$; from $\varepsilon = 1/3$ this is $(8/9)^r$. Hence $R_\delta(f) = O(\log(1/\delta)) \cdot R_{1/3}(f)$.

## Proof sketch

The majority errs only if at least $r$ of the $2r$ runs err; the probability is at most $\binom{2r}{r}\varepsilon^r(1-\varepsilon)^r \le (4\varepsilon(1-\varepsilon))^r$.

## Depends on

- [Public-coin randomized protocol](../randomized-communication-protocols/public-coin-protocol.md)
- [Randomized communication complexity](../randomized-communication-protocols/rand-complexity.md)

## Sources

- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
