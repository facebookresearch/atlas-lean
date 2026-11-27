# A sentential form containing an empty nonterminal denotes the empty language

Let $T$ be
an alphabet and $N$ a set of nonterminals, and let $V$ assign a language over $T$ to each
nonterminal. A sentential form $X_1 \cdots X_m$ over $T$ and $N$ denotes under $V$ the
concatenation $L_1 \cdots L_m$, where $L_t = V(X_t)$ if $X_t$ is a nonterminal and $L_t = \{X_t\}$
if $X_t$ is a terminal; the empty form denotes $\{\varepsilon\}$. Let $A \in N$ with
$V(A) = \emptyset$. Then every sentential form over $T$ and $N$ in which $A$ occurs denotes the
empty language under $V$.
