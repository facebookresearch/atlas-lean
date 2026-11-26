# Smooth decoders yield large decoding matchings

If $C : \{0,1\}^k \to \Gamma^n$ has a nonadaptive $(q, c, \varepsilon)$-smooth decoder, then for every $i \in [k]$ there is a matching $M_i$ of pairwise disjoint nonempty query sets $Q \subseteq [n]$, $|Q| \le q$, with $|M_i| \ge \Omega(\varepsilon n/(c\, q))$, and for each $Q \in M_i$ a deterministic predictor $g_Q : \Gamma^Q \to \{0,1\}$ with $\Pr_x[g_Q(C(x)|_Q) = x_i] \ge \frac12 + \frac{\varepsilon}{4}$ over a uniformly random message $x$.

## Proof sketch

Keep the query sets whose average accuracy over uniform messages is at least $\frac12 + \eta$; they carry a constant fraction of the decoder's probability mass. Smoothness bounds the mass touching any single position by $c/n$, so a greedy maximal matching among good sets has size proportional to $\varepsilon n/(cq)$.

## Depends on

- [Locally decodable codes and smooth decoders](locally-decodable-codes-and-smooth-decoders.md)

## Sources

- J. Katz and L. Trevisan, "On the Efficiency of Local Decoding Procedures for Error-Correcting Codes", STOC 2000.
- S. Yekhanin, "Locally Decodable Codes", Foundations and Trends in Theoretical Computer Science 6(3), 2012.
