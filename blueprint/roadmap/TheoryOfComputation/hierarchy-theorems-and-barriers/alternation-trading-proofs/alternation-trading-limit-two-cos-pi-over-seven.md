# Alternation-trading proofs stop at exponent $2\cos(\pi/7)$

For every $c > 1$, an alternation-trading proof from the speedup and slowdown rules that SAT is not in $\mathrm{DTS}(n^c)$ exists exactly when $c < 2\cos(\pi/7) \approx 1.8019$. This proves Williams's conjecture that his time lower bound for SAT on small-space algorithms is the best these methods can give.

Fix $c > 1$, and let a refutation mean a derivation by the rules R0 (initial speedup), R1 (speedup) and R2 (slowdown) from the hypothesis $\mathrm{SAT} \in \mathrm{DTS}(n^c)$ of a line ${}^{1}\mathrm{DTS}(n^b)$ from ${}^{1}\mathrm{DTS}(n^a)$ with $b < a$.

**Theorem.** For $c > 1$ there is a refutation if and only if $c < 2\cos(\pi/7)$. In particular the rules R0 to R2 can be used to derive a contradiction only for $c < 2\cos(\pi/7)$.

For $c > 1$, the condition $c < 2\cos(\pi/7)$ is equivalent to

$$
c^3 - c^2 - 2c + 1 < 0 .
$$

Consequently alternation-trading proofs give $\mathrm{SAT} \notin \mathrm{DTS}(n^c)$ for every $c < 2\cos(\pi/7)$, and no such proof gives it for any $c \ge 2\cos(\pi/7)$, in particular not for exponents approaching $2$, as folklore had expected.

## Expansion

Work in the reduced system, which has a refutation exactly when the original one does. A pair $\langle \mu, \nu \rangle$ with $\mu \ge 1$ and $\nu > 0$ is **$c$-achievable** if, whenever $c \mu b = \nu d$, a balanced derivation (annotations matched like parentheses, starting and ending with the same number of alternations) approximately derives ${}^{a}\exists^{\mu b}\mathrm{DTS}(n^{\nu d})$ from ${}^{a}\exists^{b}\mathrm{DTS}(n^{d})$. A $c$-achievable pair with $\nu < 1/c$ yields a refutation (initialization, a $\langle \mu, \nu \rangle$ step, then a slowdown to $\mathrm{DTS}(n^{c\nu + \epsilon})$ with $c\nu + \epsilon < 1$), and conversely every refutation has this shape, so a refutation exists iff some pair generated from $\langle 1, c-1 \rangle$ (achieved by speedup-slowdown patterns of type $(10)^*$) by composition and subsumption has $\nu < 1/c$.

With $\tau(\mu, \nu) = (c - 1/\nu)\mu$, composing with $\langle \mu_1, \nu_1 \rangle$ contracts $\nu$ towards $\tau(\mu_1, \nu_1)$, and for $c > 1$, $\tau(1, c-1) = (c(c-1) - 1)/(c-1) < 1/c$ iff $c^3 - c^2 - 2c + 1 < 0$ iff $c < 2\cos(\pi/7)$. If $c < 2\cos(\pi/7)$, repeatedly composing with $\langle 1, c-1 \rangle$ (Williams's annotations $X_0 = (10)^*$ and $X_{i+1} = 1 X_i 0 X_0$) drives $\nu$ below $1/c$. If $c \ge 2\cos(\pi/7)$, induction on the generation of pairs shows every generated pair has $\tau(\mu, \nu) \ge \tau(1, c-1) \ge 1/c$ and $\nu > 1/c$, so no refutation exists. For $\mathrm{DTISP}(n^c, n^{\epsilon})$ with $0 < \epsilon < 1$ the analogous characterization uses achievable triples and a pruned computer search, with no closed form.

## Depends on

- [Alternation-trading proof](alternation-trading-proof.md)

## Proof depends on

None.

## Sources

- Sam Buss, Ryan Williams, "Limits on alternation-trading proofs for time-space lower bounds", *Computational Complexity*, 2015, doi:10.1007/s00037-015-0104-9 (Theorem 1.1, Theorem 3.25, Theorem 5.5, Lemma 2.6, Definition 3.1, Lemma 3.3, Lemma 3.9, Lemma 3.24, Lemma 4.20 and Corollary 5.3; numbering of the authors' revised journal manuscript, https://mathweb.ucsd.edu/~sbuss/ResearchWeb/npProofLimits/paper-journal.pdf).
