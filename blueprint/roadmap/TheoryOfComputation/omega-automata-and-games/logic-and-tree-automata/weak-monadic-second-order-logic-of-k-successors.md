# Weak monadic second-order logic of $k$ successors

Fix $k \ge 1$. The terms of WS$k$S are built from the constant $\varepsilon$ and first-order variables by the unary successor
functions $1, \dots, k$, written in postfix ($x12$ is the second successor of the first successor of $x$). Atomic formulas
are $s = t$, $s \le t$ and $t \in X$ for terms $s, t$ and second-order variables $X$, and formulas are closed under the Boolean
connectives and quantification $\exists x$, $\exists X$ over both kinds of variables. In the intended model, first-order
variables range over words in $\{1, \dots, k\}^*$, the nodes of the infinite $k$-ary tree, $\le$ is the prefix order, and
second-order variables range over *finite* sets of words. The logic S$k$S is the same except that set variables range over
arbitrary sets of words. A set of tuples of finite sets of words is *definable* in WS$k$S if it is the set of assignments to
the free variables of some formula that satisfy it.

## Sources

- H. Comon, M. Dauchet, R. Gilleron, F. Jacquemard, D. Lugiez, C. Löding, S. Tison and M. Tommasi, *Tree Automata Techniques and Applications*, 2008, <https://inria.hal.science/hal-03367725>: Sections 3.3.1 (syntax) and 3.3.2 (semantics, and the remark on S$k$S), and Definition 3.3.2.
