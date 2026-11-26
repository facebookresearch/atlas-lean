# Hubáček–Yogev: END-OF-METERED-LINE lies in CLS via a staircase embedding into continuous local search

END-OF-METERED-LINE reduces in polynomial time to CONTINUOUS-LOCALOPT on the unit cube; hence $\mathrm{EOML}\in\mathsf{CLS}$.

## Proof sketch

Vertices of the metered line are placed along the diagonal of a grid in a staircase pattern, each edge $x\to S(x)$ realised by an axis-parallel route moving right then up. The improvement map $g$ pushes points along the route, and the potential $p$ is defined from the meter $V$ so that it strictly improves along routes and is extended by interpolation between grid points to a Lipschitz function. Because $V$ counts steps exactly, the potential at every point on a route is determined locally from $V$ at its two endpoints, so approximate local optima of $p$ with respect to $g$ arise only at ends of lines or at vertices where $V$ miscounts, both of which are EOML solutions.

## Depends on

- [END-OF-METERED-LINE: an END-OF-LINE instance with an odometer circuit whose miscounts are solutions](end-of-metered-line.md)
- [CONTINUOUS-LOCALOPT, GENERAL-CONTINUOUS-LOCALOPT and the class CLS of Daskalakis–Papadimitriou](../continuous-local-search-and-gradient-descent/continuous-localopt-and-cls.md)

## Sources

- Pavel Hubáček and Eylon Yogev, "Hardness of Continuous Local Search: Query Complexity and Cryptographic Lower Bounds", SODA (2017) and SIAM Journal on Computing (2020), ECCC TR16-063.
