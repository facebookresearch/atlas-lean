# Partial MCSP (MCSP*)

A *partial truth table* is $T \in \{0, 1, *\}^{2^n}$, describing a partial function $f^*$ on $\{0,1\}^n$. *Partial MCSP* ($\mathrm{MCSP}^*$) is the language of pairs $(T, s)$ such that some total $f$ agreeing with $f^*$ on every defined input has $\mathrm{CC}(f) \le s$, equivalently $\mathrm{CC}_S(f^*) \le s$ for the set $S$ of defined inputs. Variants measure size by binary gates only, or by De Morgan formula size, and encode $s$ in unary or binary.

## Depends on

- [The Minimum Circuit Size Problem MCSP and Gap-MCSP](minimum-circuit-size-problem.md)

## Sources

- R. Ilango, "Constant Depth Formula and Partial Function Versions of MCSP are Hard", FOCS 2020.
- S. Hirahara, "NP-Hardness of Learning Programs and Partial MCSP", FOCS 2022.
