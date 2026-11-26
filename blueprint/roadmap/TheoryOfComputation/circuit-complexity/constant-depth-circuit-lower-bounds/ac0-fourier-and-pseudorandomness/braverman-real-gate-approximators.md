# Braverman's real gate approximators

Over $\mathbb{R}$, the conjunction of bits $b_1,\dots,b_K$ is approximated by the polynomial $\prod_{c=1}^{t}\bigl(1-\sum_{j\in S_c}(1-b_j)\bigr)$ for a random family of subsets $S_1,\dots,S_t\subseteq\{1,\dots,K\}$ (each element included with geometrically decreasing probabilities), and dually for disjunctions. For every input distribution, such an approximator of degree $O(\log K\cdot\log(1/\varepsilon))$ agrees with the gate except with probability $\varepsilon$, and composing approximators over a depth-$d$ circuit of size $s$ yields a polynomial of degree $(\log s\log(1/\varepsilon))^{O(d)}$ that agrees with the circuit on all but an $\varepsilon$ fraction of the input mass.

## Proof sketch

This is the Razborov–Smolensky probabilistic-polynomial construction carried out over the reals: if some $b_j=0$, a random subset catches exactly one zero with constant probability, making a factor vanish; repetition drives the failure probability down.

## Depends on

- [Unbounded fan-in signature](../../unbounded-fan-in-circuits/ac-signature.md)
- [k-wise independent and almost k-wise independent distributions](k-wise-independent-distributions.md)

## Sources

- Mark Braverman, "Polylogarithmic Independence Fools AC^0 Circuits", Journal of the ACM, 2010.
- Alexander A. Razborov, "Lower Bounds on the Size of Bounded Depth Circuits over a Complete Basis with Logical Addition", Mathematical Notes of the Academy of Sciences of the USSR, 1987.
- Avishay Tal, "Tight Bounds on the Fourier Spectrum of AC^0", 32nd Computational Complexity Conference (CCC 2017), 2017.
