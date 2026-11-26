# Tal's bound on level-l Fourier mass of constant-depth circuits

For every Boolean function $F : \{\pm1\}^m \to \{\pm1\}$ computed by an $\mathrm{AC}^0$ circuit of depth $d$ and size $s$, and every $\ell \ge 1$,

$$
L_{1,\ell}(F) := \sum_{S \subseteq [m],\, |S| = \ell} |\hat F(S)| \le \big(c \log s\big)^{(d-1)\ell}
$$

for an absolute constant $c$. The bound is preserved under restrictions, since restrictions of the circuit have the same depth and size.

## Proof sketch

Håstad's switching lemma shows that a random restriction with survival probability $p \approx 1/(\log s)^{d-1}$ collapses the circuit to a shallow decision tree with high probability. For a decision tree of depth $t$, $L_{1,\ell} \le \binom{t}{\ell}$. Comparing the Fourier coefficients of $F$ with those of its random restrictions, which scale level-$\ell$ mass by $p^\ell$, gives the bound.

## Depends on

- [The class $\mathsf{AC}^0$](../../complexity-classes/time-and-space-complexity-classes/ac0.md)

## Proof depends on

- [Håstad's switching lemma](../../circuit-complexity/lower-bounds-for-ac0-circuits/hastad-s-switching-lemma.md)

## Sources

- Avishay Tal, "Tight bounds on the Fourier spectrum of AC0", CCC (2017); ECCC TR14-174.
- Ran Raz, Avishay Tal, "Oracle separation of BQP and PH", Journal of the ACM 69(4) (2022), STOC (2019); ECCC TR18-107.
