# END-OF-METERED-LINE and END-OF-POTENTIAL-LINE are polynomial-time equivalent, so EOPL is contained in CLS

Recall END-OF-POTENTIAL-LINE: given circuits $S,P:\{0,1\}^n\to\{0,1\}^n$ with $P(0^n)=0^n\ne S(0^n)$ and $V:\{0,1\}^n\to\{0,\dots,2^m-1\}$ with $V(0^n)=0$, find $x$ with $S(P(x))\ne x\ne0^n$ or $P(S(x))\ne x$ (R1), or $x$ with $x\ne S(x)$, $P(S(x))=x$ and $V(S(x))\le V(x)$ (R2); EOPL is the class of problems reducible to it. END-OF-METERED-LINE and END-OF-POTENTIAL-LINE are polynomial-time equivalent. Consequently $\mathsf{EOPL}\subseteq\mathsf{CLS}$.

## Proof sketch

EOML reduces to EOPL directly: a meter that increases by exactly one is a strictly increasing potential, and each EOPL solution is an EOML solution. Conversely, whenever $S(x)=y$, $P(y)=x$ and $V(y)>V(x)+1$, insert a chain of $V(y)-V(x)-1$ dummy vertices $(x,1),(x,2),\dots$ between $x$ and $y$ with consecutive meter values; successor, predecessor and meter of dummies are computed locally from $x$, and every EOML solution of the new instance maps back to an EOPL solution. The inclusion follows from EOML in CLS.

## Depends on

- [END-OF-METERED-LINE: an END-OF-LINE instance with an odometer circuit whose miscounts are solutions](end-of-metered-line.md)
- [CONTINUOUS-LOCALOPT, GENERAL-CONTINUOUS-LOCALOPT and the class CLS of Daskalakis–Papadimitriou](../continuous-local-search-and-gradient-descent/continuous-localopt-and-cls.md)

## Proof depends on

- [Hubáček–Yogev: END-OF-METERED-LINE lies in CLS via a staircase embedding into continuous local search](end-of-metered-line-in-cls.md)

## Sources

- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", ICALP (2019), arXiv:1811.03841.
- Pavel Hubáček and Eylon Yogev, "Hardness of Continuous Local Search: Query Complexity and Cryptographic Lower Bounds", SODA (2017) and SIAM Journal on Computing (2020), ECCC TR16-063.
