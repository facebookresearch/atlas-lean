# Constraint system games and entangled constraint satisfaction problems

An entangled constraint satisfaction problem asks, for a constraint system built from a fixed finite set of constraints, whether players sharing finite-dimensional entanglement win its constraint system game with probability 1 or with probability below a fixed bound.

**Constraint systems.** A *constraint* over a finite alphabet $\Sigma$ is a pair $(V, C)$ of a finite set $V$ of variables, the context, and a set $C \subseteq \Sigma^V$ of satisfying assignments. A *constraint system* (CS) is $S = (X, \{(V_i, C_i)\}_{i=1}^m)$ with a finite set $X$ of variables and constraints $(V_i, C_i)$, $V_i \subseteq X$; it is *satisfiable* if some $f : X \to \Sigma$ has $f|_{V_i} \in C_i$ for every $i$. For a map $r : V \to W$, the *pushforward* of $C \subseteq \Sigma^V$ is $r_* C = \{\varphi \in \Sigma^W : \varphi \circ r \in C\}$. For a finite set $\Gamma$ of constraints over $\Sigma$, $\mathrm{CSP}(\Gamma)$ is the set of constraint systems all of whose constraints have the form $(W_i, (r_i)_* C_i)$ with $(V_i, C_i) \in \Gamma$ and $r_i : V_i \to W_i$; its classical decision problem $\mathrm{CSP}(\Gamma)_{1,1}$ asks whether a given system in $\mathrm{CSP}(\Gamma)$ is satisfiable. Examples are 3SAT and $k$-coloring, where $\Sigma = \mathbb Z_k$ and $\Gamma = \{\neq_{\mathbb Z_k}\}$ with $\neq_{\mathbb Z_k} = \{(a, b) \in \mathbb Z_k^2 : a \neq b\}$. A constraint $(V, C)$ is *two-variable falsifiable* (TVF) if for all distinct $x, y \in V$ there are $a, b \in \Sigma$ such that no $\varphi$ with $\varphi(x) = a$ and $\varphi(y) = b$ lies in $C$; a set $\Gamma$ is TVF if all its constraints are.

**Constraint–variable game.** For a CS $S$ over $\mathbb Z_k$ and a probability distribution $\pi$ on $[m]$, in the *constraint–variable game* the referee samples $i$ from $\pi$ and then a uniformly random variable $x \in V_i$; one player receives $i$ and answers an assignment $\varphi \in C_i$, the other receives $x$ and answers $a \in \mathbb Z_k$, and they win iff $\varphi(x) = a$. In the *constraint–constraint game* both players receive constraints and must answer satisfying assignments that agree on the shared variables. The *synchronous quantum value* of such a game is the supremum of its winning probability over synchronous strategies on finite-dimensional Hilbert spaces, in the sense of [synchronous games](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/synchronous-two-prover-games.md).

**Promise problems.** For $1 \geq c \geq s \geq 0$:

- $\mathrm{SuccinctCSP}_{c\text{-}v}(\Gamma)^*_{c,s}$ has as instances probabilistic Turing machines $M$ that sample the constraints of a system $S \in \mathrm{CSP}(\Gamma)$ according to a distribution $\pi$; $M$ is a yes instance if the constraint–variable game of $(S, \pi)$ has synchronous quantum value at least $c$, and a no instance if it is less than $s$;
- $\mathrm{CSP}_{c\text{-}v}(\Gamma)^*_{c,s}$ is the same problem for systems $S \in \mathrm{CSP}(\Gamma)$ given explicitly, with $\pi$ uniform on $[m]$.

The variants $\mathrm{SuccinctCSP}_{c\text{-}c}$ and $\mathrm{CSP}_{c\text{-}c}$ use the constraint–constraint game. The source defines the yes and no instances through the defect of finite-dimensional tracial states on algebras attached to $S$; these correspond to the synchronous quantum values above.

## Depends on

- [Two-player nonlocal games: classical and entangled values](../../two-player-nonlocal-games-classical-and-entangled-values.md)
- [Synchronous two-prover games](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/synchronous-two-prover-games.md)
- [NP-complete decision problems](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

None.

## Expansion

Classically, $\mathrm{CSP}(\Gamma)_{1,1}$ is either in P or NP-complete by the CSP dichotomy theorem of Bulatov and Zhuk, and when it is NP-complete the succinct gap problem $\mathrm{SuccinctCSP}(\Gamma)_{1,s}$ is NEXP-complete for some constant $s < 1$. The entangled problems replace satisfying assignments by quantum strategies, in which the measurements for different constraints need not commute. 1-in-3-SAT, with the constraint $\{(1,0,0), (0,1,0), (0,0,1)\}$, is NP-complete and TVF; 3SAT is not TVF.

## Sources

- E. Culf and K. Mastel, "RE-completeness of entangled constraint satisfaction problems", in *2025 IEEE 66th Annual Symposium on Foundations of Computer Science (FOCS 2025)*, IEEE, 2025, pp. 2194–2230, doi:10.1109/FOCS63196.2025.00116; read as arXiv:2410.21223v2, <https://arxiv.org/abs/2410.21223v2>: Section 2 (nonlocal games, synchronous values), Section 3.1 (Definitions 3.1 and 3.2 of constraints and constraint systems, Definition 3.3 and the constraint system games described after it) and Section 4 (Definitions 4.1 and 4.2 of pushforward constraints and $\mathrm{CSP}(\Gamma)$, Definition 4.11 of entangled constraint systems and Definition 4.12 of TVF constraints).
