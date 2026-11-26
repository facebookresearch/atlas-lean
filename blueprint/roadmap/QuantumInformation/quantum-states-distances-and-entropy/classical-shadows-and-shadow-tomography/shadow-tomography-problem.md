# The shadow tomography problem

Given $N$ copies of an unknown $D$-dimensional state $\rho$, two-outcome observables $0 \preceq E_1, \dots, E_M \preceq I$, accuracy $\varepsilon > 0$ and confidence $\delta > 0$, output estimates $b_1, \dots, b_M$ with $|b_i - \mathrm{Tr}(E_i\rho)| \le \varepsilon$ for all $i$ simultaneously, with probability at least $1 - \delta$. The *sample complexity* is the least $N$ for which this is possible; collective (entangled) measurements on all copies are allowed unless stated otherwise.

## Depends on

- [Trace distance: metric, operational form and contractivity](../remaining-clauses-of-trace-distance-and-contractivity.md)

## Sources

- Scott Aaronson, "Shadow tomography of quantum states", STOC (2018), SIAM Journal on Computing 49(5) (2020); arXiv:1711.01053.
