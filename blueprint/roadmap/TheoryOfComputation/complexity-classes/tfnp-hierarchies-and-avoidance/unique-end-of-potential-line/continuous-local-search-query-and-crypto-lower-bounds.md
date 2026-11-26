# Hubáček–Yogev: exponential randomized query lower bound and obfuscation-based hardness for continuous local search

(i) The randomized query complexity of END-OF-METERED-LINE, with $S,P,V$ given as oracles on $\{0,1\}^n$, is $\Omega(2^{n/2}/\sqrt n)$. Consequently any randomized algorithm solving CONTINUOUS-LOCALOPT to $n$ digits of precision with oracle access to $p$ and $g$ makes $2^{\Omega(n)}$ queries.

(ii) Recall SINK-OF-VERIFIABLE-LINE: given $x_s$, a target $T\le2^n$ and circuits $S$, $W$ promised to satisfy $W(x,i)=1$ iff $x=S^{i-1}(x_s)$, find $x_f$ with $W(x_f,T)=1$. There is a polynomial-time reduction from SINK-OF-VERIFIABLE-LINE to END-OF-METERED-LINE whose output instances contain a single line. Hence, if one-way permutations and indistinguishability obfuscation for $\mathsf{P/poly}$ exist, END-OF-METERED-LINE, and therefore CLS and PLS, are hard for polynomial-time algorithms.

## Proof sketch

For (i), hide a random metered line inside the cube; each query reveals the line only at the queried vertex, and the meter only certifies distances, so an adversary argument shows that a randomized algorithm needs $\Omega(2^{n/2}/\sqrt n)$ queries to reach the end. Composing with the EOML-to-CLS reduction transfers the bound. For (ii), reversibility is obtained with the reversible-pebbling trick of Bitansky–Paneth–Rosen: a vertex of the new line records a pebbling configuration on the verifiable line, the meter is computed from the configuration's position in the pebbling schedule, and hardness of SINK-OF-VERIFIABLE-LINE under the stated assumptions (Garg–Pandey–Srinivasan) carries over.

## Depends on

- [Indistinguishability and virtual black-box obfuscation](../../../../ComputerScience/cryptography/program-obfuscation/indistinguishability-and-virtual-black-box.md)
- [END-OF-METERED-LINE: an END-OF-LINE instance with an odometer circuit whose miscounts are solutions](end-of-metered-line.md)
- [CONTINUOUS-LOCALOPT, GENERAL-CONTINUOUS-LOCALOPT and the class CLS of Daskalakis–Papadimitriou](../continuous-local-search-and-gradient-descent/continuous-localopt-and-cls.md)

## Proof depends on

- [Hubáček–Yogev: END-OF-METERED-LINE lies in CLS via a staircase embedding into continuous local search](end-of-metered-line-in-cls.md)

## Sources

- Pavel Hubáček and Eylon Yogev, "Hardness of Continuous Local Search: Query Complexity and Cryptographic Lower Bounds", SODA (2017) and SIAM Journal on Computing (2020), ECCC TR16-063.
