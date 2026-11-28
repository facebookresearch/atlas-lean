# The complement of the convergence problem for analytic machines is equivalent to the third real halting problem

The complement of the convergence problem for analytic machines, whether a real-number machine printing a sequence of vectors fails to
produce a convergent infinite one, is BSS many-one equivalent to the twice-iterated real halting problem, so convergence is strictly harder than
boundedness.

**Theorem.** Let $\mathbb{H}$ be the BSS halting problem and $\preceq$ BSS many-one reducibility, as in [Blum-Shub-Smale machines and their halting problems](blum-shub-smale-machines-their-halting-problems.md), and let

$$
\mathbb{K} = \{(\langle \mathcal{M} \rangle, \vec x) : \mathcal{M} \text{ on input } \vec x \text{ produces a convergent infinite sequence}\}
$$

be the *convergence problem* for [analytic machines](analytic-machines.md); a machine that prints only finitely many vectors counts as divergent (Definition 3.10 of the source). Then:

1. the complement of $\mathbb{K}$ is BSS many-one reducible to $\mathbb{H}^{\mathbb{H}^{\mathbb{H}}}$;
2. conversely, $\mathbb{H}^{\mathbb{H}^{\mathbb{H}}}$ is BSS many-one reducible to the complement of $\mathbb{K}$.

The same theorem shows that the sets BSS many-one reducible to $\mathbb{K}$ are exactly the *naïvely semidecidable* ones, those for which some weakly
analytic machine converges to $0$ on members and diverges on non-members. Since $\mathbb{H}^{\mathbb{H}^{\mathbb{H}}}$ is strictly harder than $\mathbb{H}^{\mathbb{H}}$, to which the
boundedness problem is equivalent, convergence is strictly harder than boundedness. That $\mathbb{K}$ is undecidable for weakly analytic machines was
shown earlier by diagonalization.

## Depends on

- [Blum-Shub-Smale machines and their halting problems](blum-shub-smale-machines-their-halting-problems.md)
- [Analytic machines](analytic-machines.md)

## Proof depends on

None.

## Expansion

Both parts use Cucker's characterization: a set is BSS many-one reducible to $\mathbb{H}^{\mathbb{H}^{\mathbb{H}}}$ exactly when it has the form
$\{\vec x : \exists u\ \forall v\ \exists w\ (\vec x, u, v, w) \in W\}$ with $u, v, w \in \mathbb{N}$ and $W$ BSS-decidable. A real sequence fails to converge exactly when
$\exists k\ \forall K\ \exists n, m \ge K$ with $|y_n - y_m| \ge 1/k$, and whether a machine prints such $y_n, y_m$ within $\ell$ steps is BSS-decidable, which gives the
first part. For the second, given a set of that form, run for every $u$ in parallel a procedure that keeps printing $0$ and prints $2^{-u}$ each
time it finds a witness $w$ for the next $v$. If $\forall v\ \exists w$ holds for some $u$, the output has the two accumulation points $0$ and $2^{-u}$ and
diverges; otherwise it converges to $0$. A good expansion links Cucker's characterization of the third level, which the proof cites.

## Sources

- T. Gärtner and M. Ziegler, "Real analytic machines and degrees", *Logical Methods in Computer Science* 7(3), paper 11, 2011, doi:10.2168/LMCS-7(3:11)2011; read in arXiv:1006.0398v3: Theorem 3.11 (c) and (d), with parts (a) and (b), Definition 3.10 and the remark before the proof in Section 3.3, with Cucker's characterization of the third level, which the proof cites.
