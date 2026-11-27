# Tree automata on infinite trees

For a finite alphabet $A$, an *infinite (binary) tree* over $A$ is a map $t : \{0, 1\}^* \to A$, labelling every node of the full binary
tree, where $w0$ and $w1$ are the left and right successors of $w$; $T^\omega_A$ is the set of such trees. A *Muller tree automaton* is
$\mathcal{A} = (Q, A, q_0, \Delta, \mathcal{F})$ with a finite set $Q$ of states, an initial state $q_0$, a transition relation
$\Delta \subseteq Q \times A \times Q \times Q$ and a family $\mathcal{F} \subseteq 2^Q$. A *run* on $t$ is a tree $\rho : \{0, 1\}^* \to Q$ with
$\rho(\varepsilon) = q_0$ and $(\rho(w), t(w), \rho(w0), \rho(w1)) \in \Delta$ for every node $w$. It is *successful* if along every infinite path
$\pi \in \{0, 1\}^\omega$ the set $\mathrm{In}(\rho|\pi)$ of states occurring infinitely often on $\pi$ belongs to $\mathcal{F}$, and $\mathcal{A}$
accepts $t$ if some run on $t$ is successful; $T^\omega(\mathcal{A})$ is the set of accepted trees.

Büchi, Rabin and Streett tree automata replace $\mathcal{F}$ by the corresponding condition on $\mathrm{In}(\rho|\pi)$ for every path. A
*parity* (Rabin chain) tree automaton has a chain $E_1 \subset F_1 \subset E_2 \subset \dots \subset E_n \subset F_n$ of sets of states, and a
run is successful if on every path $\pi$ some $k$ has $\mathrm{In}(\rho|\pi) \cap E_k = \emptyset$ and $\mathrm{In}(\rho|\pi) \cap F_k \ne \emptyset$;
equivalently, with $F_0 = \emptyset$, indexing the states of $E_i \setminus F_{i-1}$ by $2i - 1$, those of $F_i \setminus E_i$ by $2i$ and those outside $F_n$ by
$2n + 1$, the least index occurring infinitely often on every path is even. A set of trees is *recognizable* if it is $T^\omega(\mathcal{A})$ for a Muller tree automaton
$\mathcal{A}$; Muller, Rabin and Streett tree automata recognize the same sets.

## Sources

- W. Thomas, "Languages, automata, and logic", Bericht 9607, Institut für Informatik und Praktische Mathematik, Universität Kiel, May 1996 (preprint of the chapter in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997; numbering of the preprint): Section 2.1 (infinite trees), Definition 6.1 (Muller tree automata), Definition 6.4 (Rabin chain or parity tree automata) and the remarks after Definition 6.1.
