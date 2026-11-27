# Büchi emptiness via Kosaraju's SCC algorithm

Let $A$ be a nondeterministic Büchi automaton with a finite state set $Q$, a finite alphabet $\Sigma$, start states $I$, accepting states $F$ and a decidable transition relation, with membership in $I$ and $F$ decidable, together with a fixed enumeration of $\Sigma$; the states carry decidable equality, a Boolean equality test that agrees with it, and a hash function, which the traversals, the transpose and the scanner use. Fix a duplicate-free list $q_1, \dots, q_{|Q|}$ of all states. The transition graph $G_A$ has this vertex list, and the adjacency list of $s$ lists, in vertex-list order, the states $t$ with $s \xrightarrow{a} t$ for some $a \in \Sigma$. Write $s \to^* t$ for reachability in this graph (reflexive-transitive closure of one-step transitions). A list of states is cyclic if it contains two distinct states, or a state with a transition to itself.

Throughout, a directed graph $G$ on a finite vertex type $V$ is given by a duplicate-free list $v_1, \dots, v_{|V|}$ of all vertices and, for each vertex $v$, an ordered adjacency list $\mathrm{adj}_G(v)$ of out-neighbors (entries may repeat). The transpose $G^{T}$ has the same vertex list, and $\mathrm{adj}_{G^T}(v)$ lists, once each and in vertex-list order, the vertices $u$ with $v \in \mathrm{adj}_G(u)$. Kosaraju's algorithm runs a left-first depth-first search of $G$ with roots $v_1, \dots, v_{|V|}$ in that order, lists the vertices in decreasing order of finishing time, runs a depth-first search of $G^T$ with roots taken in that order, and cuts the preorder of this second search at its forest roots; the resulting lists are the Kosaraju blocks.

Let $R$ be the preorder of a depth-first search of $G_A$ whose roots are the start states in vertex-list order, that is, the states reachable from a start state. The emptiness scanner returns true exactly when no Kosaraju block of $G_A$ is cyclic and contains an accepting state that lies in $R$.

The following holds, with $V = |Q|$, $E$ and $E_2$ the total lengths of the adjacency lists of $G_A$ and of its transpose.

1. The scanner returns true if and only if $L_\omega(A) = \emptyset$.
2. $A$ has a lasso (a start state $s_0$ and an accepting state $s$ with a finite word leading from $s_0$ to $s$ and a nonempty finite word leading from $s$ back to $s$) if and only if there are $s_0 \in I$ and $s \in F$ with $s_0 \to^* s$ such that $s$ lies in a cyclic Kosaraju block.
3. $L_\omega(A) = \emptyset$ if and only if no Kosaraju block is cyclic and contains an accepting state $s$ with $s_0 \to^* s$ for some $s_0 \in I$.
4. There are $n_1, n_2, n_3, c_{\mathrm{split}}, c_{\mathrm{scan}} \in \mathbb{N}$ such that: the whole-graph search, the search of the transpose in decreasing finishing order, and the search from the start states, each run as the step-by-step depth-first-search machine from its initial state, halt with an empty work stack and output the respective search after exactly $n_1$, $n_2$, $n_3$ steps, where

    $$n_1 = 2V + E, \qquad n_2 = R_2 + P_2 + \sum_{v \in \mathrm{pre}_2} \lvert \mathrm{adj}_{G_A^T}(v) \rvert, \qquad n_3 = \lvert I \rvert + \lvert R \rvert + \sum_{v \in R} \lvert \mathrm{adj}_{G_A}(v) \rvert,$$

    with $R_2$ the length of the decreasing finishing order, $\mathrm{pre}_2$ the preorder of the second search and $P_2$ its length; $c_{\mathrm{split}}$ is the counted cost of cutting $\mathrm{pre}_2$ at the forest roots and satisfies $c_{\mathrm{split}} \le (\text{number of forest roots}) + 2 P_2 + 1$; $c_{\mathrm{scan}}$ is the counted cost of the scanner and satisfies

    $$c_{\mathrm{scan}} \le \lvert R \rvert + \sum_{B} \Bigl(1 + \sum_{s \in B} \lvert \mathrm{adj}_{G_A}(s) \rvert + 2 \lvert B \rvert \Bigr),$$

    the outer sum over the Kosaraju blocks $B$; and

    $$n_1 + n_2 + n_3 + c_{\mathrm{split}} + c_{\mathrm{scan}} \le 14 V + 1 + 3 (E + E_2).$$

Here $\lvert I \rvert$ stands for the number of start states in the vertex list. The numbers $n_1, n_2, n_3$ count depth-first-search machine transitions; $c_{\mathrm{split}}$ and $c_{\mathrm{scan}}$ are the costs of the specified tests (list-emptiness, block-length, examined adjacency entries, acceptance and reachability tests) and hash-table operations of the splitter and the scanner. The cost of building adjacency lists is not counted, so this is not a wall-clock linear-time bound.

## Sources

- C. Courcoubetis, M. Y. Vardi, P. Wolper, and M. Yannakakis, "Memory-efficient algorithms for the verification of temporal properties", *Formal Methods in System Design* 1 (1992), 275-288: background on Büchi emptiness; its algorithms avoid constructing the strongly connected components, and it is not the source of the split and scan costs stated here, which belong to the specified machine.
- M. Sharir, "A strong-connectivity algorithm and its applications in data flow analysis", *Computers & Mathematics with Applications* 7 (1981), 67-72, for the two-pass strongly connected component method.
