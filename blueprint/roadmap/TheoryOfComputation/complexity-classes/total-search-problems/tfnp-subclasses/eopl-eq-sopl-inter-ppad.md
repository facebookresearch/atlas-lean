# EOPL = SOPL ∩ PPAD

$\mathsf{EOPL}=\mathsf{SOPL}\cap\mathsf{PPAD}$: a total search problem reducible both to SINK-OF-POTENTIAL-LINE and to END-OF-LINE is reducible to END-OF-POTENTIAL-LINE.

## Proof sketch

$\mathsf{EOPL}\subseteq\mathsf{SOPL}\cap\mathsf{PPAD}$ holds because END-OF-POTENTIAL-LINE trivially reduces to SINK-OF-POTENTIAL-LINE (fewer solutions) and to END-OF-LINE (the pruned graph). Conversely, $\mathsf{SOPL}\cap\mathsf{PPAD}$ has the complete problem 'solve a SINK-OF-POTENTIAL-LINE instance or a bijective pigeonhole (bij-PHP) instance', and Lemma 4 of Göös et al. reduces it to END-OF-POTENTIAL-LINE: take $K$ copies of the sink-of-potential-line instance, each with a reversed copy whose sinks feed the original sources, so that non-distinguished sources disappear; add a new distinguished source $u$; and connect the $K+1$ nodes $u$ and the reversed copies of the distinguished sources to the $K$ copies of the distinguished sources according to the bij-PHP instance with $K+1$ pigeons and $K$ holes. Every end of a line of the result yields a sink of the original instance or a bij-PHP solution.

## Depends on

- [End-of-Potential-Line and the classes EOPL and SOPL](end-of-potential-line.md)

## Proof depends on

- [Inclusions among the TFNP subclasses](tfnp-subclass-inclusions.md)

## Sources

- Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao, "Further Collapses in TFNP", 37th Computational Complexity Conference (CCC 2022), arXiv:2202.07761, 2022; SIAM Journal on Computing 53(3), 2024, Lemma 4.
