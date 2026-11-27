# Collective Minimum Monotone Satisfying Assignment (CMMSA)

An instance of *CMMSA* consists of a collection $\Phi = (\varphi_1, \dots, \varphi_m)$ of monotone formulas over the variables $[n]$, a weight function $w : [n] \to \mathbb{N}$ written in unary, and a threshold $s \in \mathbb{N}$. An assignment $\alpha : [n] \to \{0, 1\}$ has weight $w(\alpha) = \sum_{i \in [n]} \alpha(i)\, w(i)$. For an integer gap $g \ge 1$ and a soundness $\varepsilon \in (0, 1]$, the promise problem $\mathrm{GapCMMSA}_{g,\varepsilon}$ (Hirahara, Definition 5.1) asks to distinguish
- (yes) some assignment $\alpha$ with $w(\alpha) \le s$ satisfies every $\varphi_j$, from
- (no) every assignment $\alpha$ with $w(\alpha) \le g\,s$ satisfies fewer than an $\varepsilon$ fraction of the formulas: $\Pr_j[\varphi_j(\alpha) = 1] < \varepsilon$ for $j$ uniform in $[m]$.

The *degree* of $\Phi$ is the largest number of literals in one of its formulas, and the size of an instance is $n$. The case $\varepsilon = 1$ is written $\mathrm{GapCMMSA}_g$: its no-instances are those in which every assignment satisfying all the formulas has weight greater than $g\,s$. Hirahara's NP-hardness theorem (Theorem 5.2) produces monotone DNF instances of degree $\Delta(n)$ with gap $\Delta(n)^{\alpha}$ and soundness $\Delta(n)^{-\alpha}$, and the reduction of his Lemma 8.3 assumes such a small soundness; $\mathrm{GapCMMSA}_g$ alone does not supply it.

## Sources

- S. Hirahara, "NP-Hardness of Learning Programs and Partial MCSP", FOCS 2022; ECCC TR22-119, Definition 5.1, Theorem 5.2 and Lemma 8.3.
- G. Kortsarz, "On the Hardness of Approximating Spanners", Algorithmica 30(3), 2001.
