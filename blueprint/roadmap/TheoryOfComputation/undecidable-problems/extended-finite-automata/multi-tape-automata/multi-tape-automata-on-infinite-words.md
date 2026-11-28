# Multi-tape automata on infinite words

A $d$-tape automaton reads $d$ infinite words in parallel, each transition consuming a nonempty word on every tape, possibly of
different lengths; a configuration is accepted from a state if some infinite run spells it out on all tapes.

Let $\mathcal{A} = A_1 \times \cdots \times A_d$ with finite alphabets $A_k$. A *$d$-tape automaton* $\mathcal{M}$ on $\mathcal{A}$
has a finite set $\mathcal{Q}$ of states and a finite set of transitions

$$
\mathcal{R} \subseteq \mathcal{Q} \times \mathcal{Q} \times (A_1^+ \times \cdots \times A_d^+) ,
$$

so every transition $(q, r, (w_1, \dots, w_d))$ reads a nonempty word $w_k$ on each tape $k$; there are no
$\varepsilon$-transitions. A *configuration* is an infinite sequence $c \in \mathcal{A}^{\mathbb{N}}$, and its $k$-th tape is
the infinite word $(c_0)_k (c_1)_k \cdots$ over $A_k$. For a state $q$, the configuration $c$ is *$q$-accepted* by $\mathcal{M}$ if
there is an infinite sequence of transitions $(q_n, r_n, (w_{n,1}, \dots, w_{n,d}))_{n \ge 1}$ with $q_1 = q$ and $r_n = q_{n+1}$ for
all $n$, such that for every $k$ the infinite word $w_{1,k} w_{2,k} \cdots$ equals the $k$-th tape of $c$.

A state $q$ is *universal* if every configuration in $\mathcal{A}^{\mathbb{N}}$ is $q$-accepted. A finite word
$x \in \mathcal{A}^*$ is a *universal prefix* for $q$ if $xy$ is $q$-accepted for every $y \in \mathcal{A}^{\mathbb{N}}$.

The words of a transition may have different lengths on different tapes, which is what makes the model powerful; if they always
have equal lengths, a $d$-tape automaton is no more powerful than a finite automaton on the product alphabet. A state may have a
universal prefix without being universal: with one tape and transitions labeled $1$, $10$ and $00$, the word $1$ is a universal
prefix but configurations starting with $01$ are rejected.

## Depends on

None.

## Proof depends on

None.

## Sources

- T. Jolivet and J. Kari, "Undecidable properties of self-affine sets and multi-tape automata", in *Mathematical Foundations of Computer Science 2014*, Lecture Notes in Computer Science 8634, pp. 352–364, Springer, 2014, doi:10.1007/978-3-662-44522-8_30; numbering of the version arXiv:1401.0705v2: Section 2.1, Remark 2.2, Section 2.3 (universal states and universal prefixes) and Example 2.4.
