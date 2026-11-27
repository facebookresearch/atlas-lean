# Partial derivatives are normalized Brzozowski derivatives

Define $\mathrm{pset}$ from regular expressions to finite sets of regular expressions by $\mathrm{pset}\,0 = \emptyset$, $\mathrm{pset}\,1 = \{1\}$, $\mathrm{pset}\,b = \{b\}$,
$\mathrm{pset}(r + s) = \mathrm{pset}\,r \cup \mathrm{pset}\,s$, $\mathrm{pset}(r \cdot s) = \mathrm{pset}\,r \odot s$ and $\mathrm{pset}(r^*) = \{r^*\}$. Then for every letter $a$ and regular expression $r$,

$$\mathrm{pset}(\partial_a r) = \mathrm{pder}_a r:$$

the [partial derivative](antimirov-partial-derivatives.md) is the [Brzozowski derivative](brzozowski-derivatives.md) with its sums split into a set, also inside the left factor of a concatenation, and $0$ dropped (Nipkow and Traytel).
Representing a finite set by an ordered sum, partial derivatives can therefore be simulated on plain regular expressions by a
normalization that erases $0$s and distributes concatenation over sums on the left; this normalization and ACI equivalence are
incomparable.

## Depends on

- [Brzozowski derivatives of regular expressions](brzozowski-derivatives.md)
- [Antimirov partial derivatives](antimirov-partial-derivatives.md)

## Sources

- T. Nipkow and D. Traytel, "Unified decision procedures for regular expression equivalence", *Interactive Theorem Proving (ITP 2014)*, Lecture Notes in Computer Science 8558, Springer, 2014, author copy <https://www21.in.tum.de/~nipkow/pubs/regex_equiv.pdf>: Section 4.2, the function $\mathrm{pset}$, the identity $\mathrm{pset}\,(\mathrm{der}\,a\,r) = \mathrm{pder}\,a\,r$ ("a direct connection between pder and der that seems not to have been covered in the literature") and the normalization that follows it.
