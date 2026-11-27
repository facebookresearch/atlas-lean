# Counter nets

A $k$-dimensional counter net is a nondeterministic finite automaton with $k$ counters over the natural numbers that every transition changes by a fixed integer vector, with no zero tests; a word is accepted when some run from the zero vector reaches an accepting state without a counter going negative.

Let $k\ge0$. A *$k$-dimensional counter net* ($k$-CN) is a tuple $\mathcal A=(\Sigma,Q,Q_0,\delta,F)$ with a finite alphabet $\Sigma$, a finite set $Q$ of states, initial states $Q_0\subseteq Q$, accepting states $F\subseteq Q$ and a finite set of transitions $\delta\subseteq Q\times\Sigma\times\mathbb Z^k\times Q$; the vector $\mathbf e$ of a transition $(p,\sigma,\mathbf e,q)$ is its *effect*. It is *deterministic* ($k$-DCN) if $|Q_0|=1$ and each pair $(p,\sigma)$ has at most one transition.

A *configuration* is a pair $(q,\mathbf v)\in Q\times\mathbb N^k$. A run on $w=\sigma_1\cdots\sigma_n$ is a sequence of configurations $(q_0,\mathbf v_0),\dots,(q_n,\mathbf v_n)$ with $(q_{i-1},\sigma_i,\mathbf v_i-\mathbf v_{i-1},q_i)\in\delta$ for every $i$; since every $\mathbf v_i$ lies in $\mathbb N^k$, a transition can be taken only if no counter becomes negative. The run is *accepting* if $q_0\in Q_0$, $\mathbf v_0=\mathbf 0$ and $q_n\in F$, and the *language* $L(\mathcal A)\subseteq\Sigma^*$ is the set of words with an accepting run. A $0$-CN is a nondeterministic finite automaton, so $0$-CNs accept exactly the regular languages, and $k$-CNs are vector addition systems with states whose transitions carry input letters.

**Compositeness and primality.** For $d,n\in\mathbb N$, a $k$-CN $\mathcal A$ is *$(d,n)$-composite* if there are $d$-CNs $\mathcal B_1,\dots,\mathcal B_n$ with

$$
L(\mathcal A)=\bigcap_{i=1}^nL(\mathcal B_i).
$$

It is *composite* if it is $(d,n)$-composite for some $d<k$ and some $n$, and *prime* otherwise; it is *dimension-minimal* if it is not $(k-1,1)$-composite, that is, if no counter net of smaller dimension accepts the same language. Being $(0,1)$-composite means accepting a regular language.

## Depends on

None.

## Proof depends on

None.

## Expansion

Every $k$-DCN is $(1,k)$-composite: projecting its transitions onto each counter gives $k$ deterministic one-counter nets with the same state structure whose languages intersect to $L(\mathcal A)$. A deterministic counter net is therefore prime only in dimension $0$, or in dimension $1$ when its language is not regular. Primality thus measures what nondeterminism together with several counters can express beyond intersections of lower-dimensional languages.

## Sources

- Shaull Almagor, Guy Avni, Henry Sinclair-Banks and Asaf Yeshurun, "Dimension-Minimality and Primality of Counter Nets", in *Foundations of Software Science and Computation Structures (FoSSaCS 2024)*, Lecture Notes in Computer Science, Springer, 2024, pp. 229–249, doi:[10.1007/978-3-031-57231-9_11](https://doi.org/10.1007/978-3-031-57231-9_11); read in arXiv:2307.14492v2 ([arXiv](https://arxiv.org/abs/2307.14492v2)): Section 2 (counter nets, runs and languages) and Section 3 (the definition of compositeness, primality and dimension-minimality, the remark on regularity, and the proposition that deterministic counter nets are $(1,k)$-composite).
