# UEOPL ⊆ EOPL ⊆ CLS = PPAD ∩ PLS

$\mathsf{UEOPL}\subseteq\mathsf{EOPL}\subseteq\mathsf{CLS}=\mathsf{PPAD}\cap\mathsf{PLS}$. Without the (UV3) solutions, UNIQUE-EOPL coincides with END-OF-POTENTIAL-LINE; the extra solution type makes UNIQUE-EOPL potentially easier, and problems reducible to it have the property that detecting two lines, through a second start or a (UV3) pair, immediately yields a violation of the original problem's promise.

## Proof sketch

Every instance of UNIQUE-EOPL is an END-OF-POTENTIAL-LINE instance whose (R1) and (R2) solutions are (U1), (UV2) or (UV1) solutions; since END-OF-POTENTIAL-LINE remains total, the identity reduction disallowing (UV3) shows $\mathsf{UEOPL}\subseteq\mathsf{EOPL}$. The middle inclusion is the EOML equivalence, and the final equality is the collapse of CLS.

## Depends on

- [UNIQUE-EOPL, the class UEOPL and PromiseUEOPL: one potential line certified by violation solutions](unique-eopl-and-ueopl.md)
- [CONTINUOUS-LOCALOPT, GENERAL-CONTINUOUS-LOCALOPT and the class CLS of Daskalakis–Papadimitriou](../continuous-local-search-and-gradient-descent/continuous-localopt-and-cls.md)

## Proof depends on

- [CLS = PPAD ∩ PLS, with 2D-CLS, promise-CLS and Linear-CLS equal to CLS and Banach-type contraction problems complete](../continuous-local-search-and-gradient-descent/cls-equals-ppad-cap-pls.md)
- [END-OF-METERED-LINE and END-OF-POTENTIAL-LINE are polynomial-time equivalent, so EOPL is contained in CLS](end-of-metered-line-equivalent-to-eopl.md)

## Sources

- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", ICALP (2019), arXiv:1811.03841.
- John Fearnley, Paul W. Goldberg, Alexandros Hollender and Rahul Savani, "The Complexity of Gradient Descent: CLS = PPAD ∩ PLS", STOC (2021) and Journal of the ACM 70(1) (2023), arXiv:2011.01929.
