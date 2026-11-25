# Sipser's HAMPATH instance of a CNF formula

Let $\varphi$ be a CNF formula with $m$
clauses, numbered $0, \dots, m - 1$, and let $x_0, \dots, x_{k-1}$ be its distinct variables,
in the order of their last occurrences in $\varphi$ (clauses read in order, and the literals of
each clause in order). Put $T_i = m + i(3m + 2)$ and $R_{i,l} = T_i + 1 + l$. The result is the
encoded PATH instance with vertices $0, \dots, T_k$, source $T_0$, target $T_k$, and, for each
$i < k$, the following arcs: the frame arcs $T_i \to R_{i,0}$, $T_i \to R_{i,3m}$,
$R_{i,0} \to T_{i+1}$ and $R_{i,3m} \to T_{i+1}$; the row arcs $R_{i,l} \to R_{i,l+1}$ and
$R_{i,l+1} \to R_{i,l}$ for every $l < 3m$; and, for every clause $j < m$, the arcs
$R_{i,3j+1} \to j$ and $j \to R_{i,3j+2}$ if the literal $x_i$ occurs in clause $j$, and the
arcs $R_{i,3j+2} \to j$ and $j \to R_{i,3j+1}$ if the literal $\neg x_i$ occurs in clause $j$.
