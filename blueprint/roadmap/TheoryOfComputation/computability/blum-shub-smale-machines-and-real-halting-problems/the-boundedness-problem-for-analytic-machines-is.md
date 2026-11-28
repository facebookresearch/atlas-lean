# The boundedness problem for analytic machines is not decidable relative to the real halting problem

Whether an analytic machine, a real-number machine printing a finite or infinite sequence of vectors, produces a bounded sequence on a given
input can be semidecided, but not decided, by a Blum-Shub-Smale machine with access to the real halting problem.

**Proposition.** Let $\mathbb{H}$ be the BSS halting problem, as in [Blum-Shub-Smale machines and their halting problems](blum-shub-smale-machines-their-halting-problems.md), and let

$$
\mathbb{B} = \{(\langle \mathcal{M} \rangle, \vec x) : \mathcal{M} \text{ on input } \vec x \text{ produces a bounded sequence}\}
$$

be the *boundedness problem* for [analytic machines](analytic-machines.md), where a finite output sequence counts as bounded.

1. A BSS machine with oracle access to $\mathbb{H}$ can semidecide $\mathbb{B}$.
2. No BSS machine with oracle access to $\mathbb{H}$ decides $\mathbb{B}$. More precisely, $\mathbb{H}^{\mathbb{H}} \preceq \mathbb{B}$.

So $\mathbb{B}$ lies at the level of $\mathbb{H}^{\mathbb{H}}$ in the arithmetical hierarchy over the reals: it is semidecidable relative to $\mathbb{H}$, hence
BSS many-one reducible to $\mathbb{H}^{\mathbb{H}}$ by Cucker's characterization, and $\mathbb{H}^{\mathbb{H}}$ reduces to it.

## Depends on

- [Blum-Shub-Smale machines and their halting problems](blum-shub-smale-machines-their-halting-problems.md)
- [Analytic machines](analytic-machines.md)

## Proof depends on

None.

## Expansion

For the first part, given $\mathcal{M}$ and $\vec x$, try the bounds $n = 1, 2, \ldots$ in turn and use the oracle $\mathbb{H}$ to ask whether $\mathcal{M}$ on $\vec x$
ever prints a vector of norm above $n$; the search halts exactly when some bound holds. For the reduction $\mathbb{H}^{\mathbb{H}} \preceq \mathbb{B}$, write
$\mathbb{H}^{\mathbb{H}} = \{\vec x : \exists y \in \mathbb{N}\ \forall z \in \mathbb{N}\ (\vec x, y, z) \in W\}$ with $W$ BSS-decidable, by Cucker's characterization. The
analytic machine $\mathcal{M}$, on input $\vec x$, tries $y = 1, 2, \ldots$ in turn, searching for some $z$ with $(\vec x, y, z) \notin W$; when it finds one it
outputs $y$ and moves to $y + 1$. If $\vec x \in \mathbb{H}^{\mathbb{H}}$, some $y$ makes the search run forever and the output is finite, hence bounded; otherwise
every $y$ is output and the sequence is unbounded. So $\vec x \mapsto (\langle \mathcal{M} \rangle, \vec x)$ reduces $\mathbb{H}^{\mathbb{H}}$ to $\mathbb{B}$. A good expansion links Cucker's characterization of the levels of the arithmetical hierarchy over the reals (Fact 1.3 of the source).

## Sources

- T. Gärtner and M. Ziegler, "Real analytic machines and degrees", *Logical Methods in Computer Science* 7(3), paper 11, 2011, doi:10.2168/LMCS-7(3:11)2011; read in arXiv:1006.0398v3: the definition of $\mathbb{B}$ and Proposition 3.2 with its proof in Section 3.1, and Fact 1.3 (Cucker's characterization of semidecidability relative to $\mathbb{H}$).
