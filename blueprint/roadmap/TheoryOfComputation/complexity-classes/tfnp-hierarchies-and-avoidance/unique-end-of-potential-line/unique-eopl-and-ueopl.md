# UNIQUE-EOPL, the class UEOPL and PromiseUEOPL: one potential line certified by violation solutions

**UNIQUE-EOPL.** Input as in END-OF-POTENTIAL-LINE: $S,P:\{0,1\}^n\to\{0,1\}^n$ with $P(0^n)=0^n\ne S(0^n)$, $V:\{0,1\}^n\to\{0,\dots,2^m-1\}$ with $V(0^n)=0$. Output one of:

- (U1) $x$ with $P(S(x))\ne x$ (end of a line; the proper solution);
- (UV1) $x$ with $x\ne S(x)$, $P(S(x))=x$ and $V(S(x))\le V(x)$;
- (UV2) $x$ with $S(P(x))\ne x\ne0^n$ (start of a second line);
- (UV3) $x\ne y$ with $x\ne S(x)$, $y\ne S(y)$, and $V(x)=V(y)$ or $V(x)<V(y)<V(S(x))$.

Since potentials strictly increase along lines, a (UV3) pair lies on two different lines, so (UV3) certifies multiplicity immediately even when both vertices are far from their line starts. **UEOPL** is the class of total search problems polynomial-time reducible to UNIQUE-EOPL. **PromiseUNIQUE-EOPL** is the promise problem on instances where $0^n$ is the only start of a line (no UV2 or UV3 solutions), and **PromiseUEOPL** the class of promise problems reducible to it. A reduction between problems with proper and violation solutions is **promise-preserving** if violation-free source instances map to violation-free target instances, so promise problems inherit membership.

## Depends on

- [END-OF-METERED-LINE and END-OF-POTENTIAL-LINE are polynomial-time equivalent, so EOPL is contained in CLS](end-of-metered-line-equivalent-to-eopl.md)

## Sources

- John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani, "Unique End of Potential Line", ICALP (2019), arXiv:1811.03841.
