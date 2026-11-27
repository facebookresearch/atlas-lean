# Katz–Trevisan: every locally decodable code is smooth

If $C$ has a $(q, \delta, \varepsilon)$ local decoder that is nonadaptive (or has oblivious expected reads), then $C$ has a $(q, q/\delta, \varepsilon)$-smooth decoder: replace the answers at the *heavy* positions, those read with expected count more than $q/(\delta n)$, by fixed symbols. For arbitrary adaptive $q$-query decoders over a finite alphabet $\Gamma$, guessing the first $q - 1$ answers uniformly at random yields a nonadaptive decoder with bias reduced by the factor $|\Gamma|^{q-1}$, hence a $(q, q/\delta, \varepsilon/|\Gamma|^{q-1})$-smooth decoder.

## Proof sketch

There are at most $\delta n$ heavy positions, since total expected reads are at most $q$; a word that agrees with $C(x)$ off the heavy positions is within distance $\delta n$, so the original decoder succeeds on it, and masking the heavy positions makes the decoder smooth without changing its behaviour on such words.

## Depends on

- [Locally decodable codes and smooth decoders](locally-decodable-codes-and-smooth-decoders.md)

## Sources

- J. Katz and L. Trevisan, "On the Efficiency of Local Decoding Procedures for Error-Correcting Codes", STOC 2000.
- I. Kerenidis and R. de Wolf, "Exponential Lower Bound for 2-Query Locally Decodable Codes via a Quantum Argument", Journal of Computer and System Sciences 69(3), 2004.
- S. Yekhanin, "Locally Decodable Codes", Foundations and Trends in Theoretical Computer Science 6(3), 2012.
