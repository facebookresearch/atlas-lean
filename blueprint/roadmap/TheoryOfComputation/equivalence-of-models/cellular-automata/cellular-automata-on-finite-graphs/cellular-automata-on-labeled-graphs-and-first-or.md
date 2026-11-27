# Cellular automata on labeled graphs and first-order logic on their orbits

A local rule of a cellular automaton on labeled graphs reads, around each vertex, the capped counts of states found at the ends of labeled walks of
bounded length, so one rule defines a global map on every graph; first-order logic on orbits quantifies over configurations and uses the
one-step relation of that map.

**Graphs.** For finite label sets $\Sigma$ and $\Delta$, a *$(\Sigma, \Delta)$-labeled graph* $G = (V, (E_\delta)_{\delta \in \Delta}, L)$, finite or infinite, has vertices $V$, edge relations
$E_\delta \subseteq V \times V$ and a vertex labeling $L : V \to \Sigma$; graphs are simple (at most one edge of each label between two vertices). For $v \in V$ and $w \in \Delta^*$, $\mathcal{R}^w(v)$ is the
set of vertices reachable from $v$ by a path labeled $w$, with $\mathcal{R}^\varepsilon(v) = \{v\}$. The Cayley graph of a finitely generated group with a finite symmetric generating set
$\Delta$ has an edge labeled $\delta$ from $\gamma$ to $\gamma\delta$.

**Local rules.** Let $S$ be a finite set of states. A configuration is a map $c : V \to S$. For $k \ge 1$ and $r \ge 0$, the *$k$-capped pattern of radius $r$* at $v$ in $c$ is the map
$P(c, v, r, k) : \Delta^{\le r} \times S \to \{0, \dots, k\}$ sending $(w, s)$ to the number of vertices $v' \in \mathcal{R}^w(v)$ with $c_{v'} = s$, capped at $k$. A *CA local rule* of radius $r$
with $k$-capped multisets is a map $f : \Sigma \times \{0, \dots, k\}^{\Delta^{\le r} \times S} \to S$; on every $(\Sigma, \Delta)$-labeled graph $G$ it defines the *global map*
$F_{G,f} : S^V \to S^V$ by $F_{G,f}(c)_v = f(L(v), P(c, v, r, k))$. On Cayley graphs, with $|\Sigma| = 1$, these are exactly the classical cellular automata.

**FO logic on orbits.** First-order formulas on orbits have variables ranging over configurations and atomic formulas $y = y'$ and $y \to y'$, the latter meaning that the global map
sends $y$ to $y'$ in one step; they are closed under the Boolean connectives and quantifiers. For a global map $F$ and a sentence $\phi$, $F \models \phi$ is defined in the obvious way.
For a sentence $\phi$ and a graph $G$, $\mathcal{CA}(\phi, G) = \{ f : F_{G,f} \models \phi \}$ is the *model checking problem* of $\phi$ on $G$, with local rules as inputs. The source proves
that the graph properties $\{G : F_{G,f} \models \phi\}$ defined by such pairs are exactly the properties of labeled graphs definable in monadic second-order logic.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](../cellular-automata-on-z-d.md)
- [Cayley digraph](../../../../GraphTheory/algebraic-graph-theory/part-01/directed-cayley-graph.md)
- [Group](../../../../GroupTheory/group-basics/group.md)

## Proof depends on

None.

## Sources

- G. Theyssier, "FO logic on cellular automata orbits equals MSO logic", in *51st International Colloquium on Automata, Languages, and Programming (ICALP 2024)*, LIPIcs 297, paper 154, 2024, doi:10.4230/LIPIcs.ICALP.2024.154; read in arXiv:2404.16430v1: Section 2 (graphs, CA local rules and global maps, MSO and FO formulas and their semantics, the sets of local rules defined by a formula and a graph) and the corollary of Section 4 on MSO-definable and FO/CA-definable graph languages.
