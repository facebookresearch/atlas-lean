# Katz–Trevisan length lower bound for q-query LDCs

For every $q \ge 2$, every $(q, \delta, \varepsilon)$-locally decodable code $C : \{0,1\}^k \to \Gamma^n$ with $|\Gamma| \ge 2$ satisfies

$$n \ge c(q, \delta, \varepsilon, |\Gamma|) \cdot k^{q/(q-1)}$$

for a constant $c(q, \delta, \varepsilon, |\Gamma|) > 0$ that depends only on $q$, $\delta$, $\varepsilon$ and $|\Gamma|$, for adaptive decoders as well (with a constant depending on $|\Gamma|^{q}$). For $q = 1$, the message length $k$ is bounded by a function of $\delta$, $\varepsilon$ and $\log|\Gamma|$ alone. The proof is information-theoretic and uses no linearity.

## Proof sketch

Smooth the decoder and extract decoding matchings $M_i$. A random restriction keeping each position with probability $p$ leaves, for each $i$, a surviving matching edge with probability about $1 - e^{-p^q|M_i|}$; the surviving positions then determine about $k(1 - e^{-p^q \varepsilon n/(cq)})$ message bits with bias $\Omega(\varepsilon)$, so by the information bound $|T|(1 - h(\frac12 + \eta)) \le pn\log_2|\Gamma|$ (binary entropy $h$, Pinsker) one gets $k \lesssim p n \log|\Gamma| / \varepsilon^2$; choosing $p = (cq/(\varepsilon n))^{1/q}$, so that $p^q \varepsilon n/(cq) = 1$, gives $k = O(n^{1 - 1/q})$ for fixed $q$, $\varepsilon$ and $|\Gamma|$, that is $n = \Omega(k^{q/(q-1)})$.

## Depends on

- [Locally decodable codes and smooth decoders](locally-decodable-codes-and-smooth-decoders.md)
- [Shannon entropy](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)

## Proof depends on

- [Katz–Trevisan: every locally decodable code is smooth](katz-trevisan-smoothing.md)
- [Smooth decoders yield large decoding matchings](smooth-decoders-yield-decoding-matchings.md)

## Sources

- J. Katz and L. Trevisan, "On the Efficiency of Local Decoding Procedures for Error-Correcting Codes", STOC 2000.
- S. Yekhanin, "Locally Decodable Codes", Foundations and Trends in Theoretical Computer Science 6(3), 2012.
