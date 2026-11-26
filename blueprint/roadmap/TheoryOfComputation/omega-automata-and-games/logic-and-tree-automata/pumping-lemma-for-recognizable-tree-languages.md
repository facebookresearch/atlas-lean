# Pumping lemma for recognizable tree languages

For a ground term $t$ let $\mathrm{Height}(t)$ be $1$ for a constant and $1 + \max_i \mathrm{Height}(t_i)$ for
$t = f(t_1, \dots, t_n)$. A *context* is a term $C$ with exactly one occurrence of a variable $x$, and $C[u]$ replaces $x$ by
$u$; it is *trivial* if it is $x$ itself, $C^0 = x$ and $C^{n+1} = C^n[C]$.

Let $L$ be a recognizable set of ground terms over a ranked alphabet, in the sense of
[bottom-up finite tree automata](bottom-up-finite-tree-automata.md). There is a constant $k > 0$ such that every $t \in L$ with
$\mathrm{Height}(t) > k$ can be written $t = C[C'[u]]$ for a context $C$, a nontrivial context $C'$ and a ground term $u$ such
that $C[C'^n[u]] \in L$ for every $n \ge 0$. One can take $k$ to be the number of states of an automaton recognizing $L$.

## Depends on

- [Bottom-up finite tree automata](bottom-up-finite-tree-automata.md)

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>: the Preliminaries (heights of terms and contexts) and Section 1.2, the Pumping Lemma and its proof.
- F. Gécseg and M. Steinby, *Tree Automata*, Akadémiai Kiadó, Budapest, 1984; reissued with a preface to the second edition as arXiv:1509.06233, 2015, with the original numbering: Section 2.10, Lemma 2.10.1 (with height counted from $0$ at the leaves, so its hypothesis $\mathrm{hg}(t) \ge k$ is $\mathrm{Height}(t) > k$ here).
