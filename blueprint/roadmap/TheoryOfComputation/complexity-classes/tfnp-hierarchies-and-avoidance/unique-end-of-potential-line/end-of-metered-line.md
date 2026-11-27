# END-OF-METERED-LINE: an END-OF-LINE instance with an odometer circuit whose miscounts are solutions

**END-OF-METERED-LINE (EOML).** Input: Boolean circuits $S,P:\{0,1\}^n\to\{0,1\}^n$ and $V:\{0,1\}^n\to\{0,1,\dots,2^n\}$ with $P(0^n)=0^n\ne S(0^n)$ and $V(0^n)=1$. Output a string $x$ satisfying one of:

1. $P(S(x))\ne x$, or $S(P(x))\ne x\ne0^n$ (an END-OF-LINE solution for $(S,P)$);
2. $x\ne0^n$ and $V(x)=1$ (a second vertex claiming to be the start);
3. $V(x)>0$ and $V(S(x))-V(x)\ne1$, or $V(x)>1$ and $V(x)-V(P(x))\ne1$ (a miscount).

The intended behaviour is $V(x)=i$ iff $x=S^{i-1}(0^n)$, i.e. $V$ is an odometer for the line from $0^n$; since this cannot be verified, every witnessed deviation is accepted as a solution, making the problem syntactically total.

## Depends on

- [END-OF-THE-LINE is total](../../../completeness-other-classes/ppad-and-the-end-of-the-line-problem/exists-solution.md)
- [The END-OF-THE-LINE graph](../../../completeness-other-classes/ppad-and-the-end-of-the-line-problem/adj.md)

## Sources

- Pavel Hubáček and Eylon Yogev, "Hardness of Continuous Local Search: Query Complexity and Cryptographic Lower Bounds", SODA (2017) and SIAM Journal on Computing (2020), ECCC TR16-063.
