# Li: seeded non-malleable extractors with asymptotically optimal seed length

For every constant $\gamma > 0$ there is a constant $C > 0$ such that for all $n$ and $0 < \varepsilon < 1$, with seed length $d = C\log(n/\varepsilon)$ and every min-entropy $k \ge C\log(d/\varepsilon)$, there is an explicit strong $(k, \varepsilon)$ seeded non-malleable extractor $\mathrm{nmExt} : \{0,1\}^n \times \{0,1\}^d \to \{0,1\}^m$ with output length $m = (1-\gamma)k/2$. Thus the seed length is $O(\log n + \log(1/\varepsilon))$ and the entropy requirement is only $O(\log\log n + \log(1/\varepsilon))$; these parameters are asymptotically optimal.

## Proof sketch

Li constructs advice generators and correlation breakers whose costs no longer carry an extra $\log\log$ or $\log(1/\varepsilon)$ factor: the advice is produced by encoding the source with an asymptotically good code and sampling coordinates with an optimal sampler, and the correlation breaker uses an alternating extraction protocol of length proportional to the advice length with seeded extractors of optimal seed length, so the total seed length is $O(\log n + \log(1/\varepsilon))$.

## Depends on

- [Seeded non-malleable extractors (Dodis-Wichs)](seeded-non-malleable-extractors.md)

## Proof depends on

- [Correlation breakers with advice](correlation-breakers-with-advice.md)

## Sources

- Xin Li, "Two source extractors for asymptotically optimal entropy, and (many) more", FOCS (2023); arXiv:2303.06802.
