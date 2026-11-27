# Ordered trees and progress measures

The trees here are rooted, have all leaves at the same depth and totally ordered children: a tree of height $0$ is a leaf and a tree
of height $h + 1$ is a list $[t_1, \dots, t_k]$ of trees of height $h$; its *size* is its number of leaves. For a tree $t$ of height $h$
put $d = 2h$; a leaf is the list of its directions $(D_{d-1}, D_{d-3}, \dots, D_1)$, indexed by the odd numbers below $d$ from the root down,
and $\le$ is the lexicographic order on the set $Y_t$ of leaves. For $p \in \{1, \dots, d\}$ and a leaf $\ell$ let $\ell_{\ge p}$ be the truncation
$(D_{d-1}, \dots, D_p)$, and set $\ell \lhd_p \ell'$ if $\ell_{\ge p} < \ell'_{\ge p}$ for $p$ odd and if $\ell_{\ge p} \le \ell'_{\ge p}$ for $p$ even. Add a top element
$\top$ above all leaves with $\ell \lhd_p \top$ for every $p$ and every $\ell \in Y_t \cup \{\top\}$, including $\top \lhd_p \top$.

Let $\mathcal{G}$ be a [parity game](../parity-games/parity-game.md) with priorities in $\{1, \dots, d\}$ on its edges (the linked definition puts
priorities on positions; a priority on a position can be moved to its outgoing edges). A *progress measure* over $t$ is a map
$\mu : V \to Y_t \cup \{\top\}$ such that for every vertex $u$:
some edge $u \xrightarrow{p} v$ has $\mu(v) \lhd_p \mu(u)$ if $u$ belongs to Eve, and every edge $u \xrightarrow{p} v$ has $\mu(v) \lhd_p \mu(u)$ if $u$ belongs to Adam.
Equivalently $\mu$ is a pre-fixed point, $\mathcal{O}_t(\mu) \le \mu$, of the monotone operator $\mathcal{O}_t$ built from
$\delta_t(\ell, p) = \min_\le \{\ell' : \ell \lhd_p \ell'\}$, minimizing over the edges at Eve's vertices and maximizing at Adam's.

## Depends on

- [Parity game](../parity-games/parity-game.md)
- [Universal trees](universal-trees.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.5, the definitions of trees and embeddings before Definition 2.2, "Ordering the leaves" (the relations $\lhd_p$ and Lemma 2.12) and "Progress measures" (the lattice $Y_t$, the function $\delta_t$, the operator $\mathcal{O}_t$ and the unfolded condition).
