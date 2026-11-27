# Equality of stochastic cellular automata is undecidable in dimension two and higher

Whether two stochastic cellular automata, in which each cell also reads independent uniform random symbols, define the same random map on configurations is undecidable in every dimension $d \ge 2$, both for the set of reachable images and for their probability distributions.

**Theorem.** A *stochastic cellular automaton* $\mathcal A = (Q, R, V, V', f)$ on $\mathbb Z^d$ has a finite set $Q$ of states, a finite set $R$ of random symbols, finite neighborhoods $V = \{v_1, \dots, v_\rho\}$ and $V' = \{v'_1, \dots, v'_{\rho'}\}$ in $\mathbb Z^d$, and a local function $f : Q^\rho \times R^{\rho'} \to Q$; its explicit global function is $F(c, s)_z = f\big((c_{z+v_i})_i, (s_{z+v'_j})_j\big)$ for a configuration $c \in Q^{\mathbb Z^d}$ and an $R$-configuration $s \in R^{\mathbb Z^d}$. Its *non-deterministic global function* maps $c$ to $N_F(c) = \{F(c, s) : s \in R^{\mathbb Z^d}\}$, and its *stochastic global function* maps $c$ to the measure $S_F(c)$, the image of the uniform product measure on $R^{\mathbb Z^d}$ under $s \mapsto F(c, s)$. Let $P_N$ ($P_S$) be the problem of deciding whether two given stochastic cellular automata have the same non-deterministic (stochastic) global function. For every fixed $d \ge 2$, both $P_N$ and $P_S$ are undecidable for stochastic cellular automata of dimension $d$.

Likewise it is undecidable in dimension $d \ge 2$ whether a given stochastic cellular automaton is *noisy*, that is, $N_F(c)$ is the whole configuration space for every configuration $c$ (Proposition 4.6 of the source). For correlation-free automata, in which every cell uses only its own random symbol ($V' = \{0\}$), noisiness is decidable (Theorem 5.6), but it is undecidable in dimension $d \ge 2$ whether the square $F^2$ of such an automaton is noisy, or maps every configuration to the uniform measure (Theorem 5.7).

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](cellular-automata-on-z-d.md)

## Proof depends on

- [Injectivity and surjectivity of two-dimensional cellular automata are undecidable](injectivity-and-surjectivity-are-undecidable-in-dimension-two.md)

## Expansion

Surjectivity of deterministic cellular automata reduces to both problems (Theorem 4.1). For a deterministic cellular automaton $F$ on $Q^{\mathbb Z^d}$, let $\mathcal A$ be the stochastic automaton with random symbols $R = Q$ and $G(c, s) = F(s)$, which ignores its configuration and applies $F$ to the random input. Then $S_G(c)$ is the image $\mu_F$ of the uniform measure under $F$ for every $c$, and $F$ is surjective iff $\mu_F$ is the uniform measure; similarly $N_G(c) = Q^{\mathbb Z^d}$ iff $F$ is surjective. Comparing $\mathcal A$ with the automaton that outputs its uniform random symbols decides surjectivity, which is undecidable in dimension $2$ and higher (Kari).

## Sources

- P. Arrighi, N. Schabanel and G. Theyssier, "Stochastic Cellular Automata: Correlations, Decidability and Simulations", *Fundamenta Informaticae* 126(2–3):121–156, 2013, doi:[10.3233/FI-2013-875](https://doi.org/10.3233/FI-2013-875); read as arXiv:1304.7185v2, whose numbering is used here: Definitions 3.1 and 3.2 and Section 3.3 (non-deterministic and stochastic global functions), Theorem 4.1 with its proof, Corollary 4.2, Proposition 4.6, Theorems 5.6 and 5.7.
