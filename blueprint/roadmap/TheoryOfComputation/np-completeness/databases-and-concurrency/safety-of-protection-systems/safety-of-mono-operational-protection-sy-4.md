# SAFETY OF MONO-OPERATIONAL FILE PROTECTION SYSTEMS is NP-complete

The SAFETY OF MONO-OPERATIONAL FILE PROTECTION SYSTEMS decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a set `R` of generic rights, a set `O` of objects, a set `S ⊆ O` of subjects, sets `P(s, o) ⊆ R` of rights for each subject `s ∈ S` and object `o ∈ O` (the access matrix), a finite set `C` of commands, each of the form "if `r₁ ∈ P(X₁, Y₁)` and ... and `rₘ ∈ P(Xₘ, Yₘ)` then `θ`" (`m ≥ 0`) with a single operation `θ` of the form "enter `r` into `P(X, Y)`" or "delete `r` from `P(X, Y)`", and a specified right `r' ∈ R`. Question: is there a sequence of commands from `C`, with actual parameters, such that at some point in its execution the right `r'` is entered into a set `P(s, o)` that previously did not contain `r'`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR36] SAFETY OF FILE PROTECTION SYSTEMS, p. 235 (comment: "If no command can contain more than one operation, then the problem is NP-complete in general and solvable in polynomial time for fixed systems").
- M. A. Harrison, W. L. Ruzzo and J. D. Ullman, "Protection in operating systems", Communications of the ACM 19 (1976), 461-471, doi:10.1145/360303.360333 (Section 3: the model; Section 4: safety, mono-operational systems, and NP-completeness of their safety problem by a reduction from CLIQUE).
