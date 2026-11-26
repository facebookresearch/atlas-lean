# EOPL = SOPL ∩ PPAD

$\mathsf{EOPL}=\mathsf{SOPL}\cap\mathsf{PPAD}$: a total search problem reducible both to SINK-OF-POTENTIAL-LINE and to END-OF-LINE is reducible to END-OF-POTENTIAL-LINE.

## Proof sketch

Given reductions to both problems, run the sink-of-potential-line instance and the end-of-line instance in parallel on a product graph whose potential is that of the first coordinate; every end of the combined potential line yields a sink of the first instance or an end of the second, and both map back to solutions of the original problem.

## Depends on

- [End-of-Potential-Line and the classes EOPL and SOPL](end-of-potential-line.md)

## Proof depends on

- [Inclusions among the TFNP subclasses](tfnp-subclass-inclusions.md)

## Sources

- Mika Göös et al., "Further Collapses in TFNP", 37th Computational Complexity Conference (CCC 2022), arXiv:2202.07761, 2022, Lemma 4.
