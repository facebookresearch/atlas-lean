# Counting-regular and slender languages

The counting function of a language gives the number of its words of each length. A language is counting-regular if some regular language has the same counting function, and $k$-slender if it has at most $k$ words of each length.

**Definition.** For a language $L \subseteq \Sigma^*$ let $f_L(n)$ be the number of words of length $n$ in $L$. The language $L$ is called

- *counting-regular* if there is a regular language $L'$ (over some alphabet) with $f_L(n) = f_{L'}(n)$ for all $n \ge 0$;
- *strongly counting-regular* if $L \cap L_1$ is counting-regular for every regular language $L_1$;
- *$k$-slender*, for $k \ge 1$, if $f_L(n) \le k$ for all $n$; *thin* if it is $1$-slender; and *slender* if it is $k$-slender for some $k$.

A language is *letter-bounded* if it is a subset of $a_1^* \cdots a_r^*$ for some letters $a_1, \dots, a_r$. Every regular language is counting-regular, and so is, for example, $\{ww : w \in \{a, b\}^*\}$, which has as many words of each length as $(a(a+b))^*$. Languages of unambiguous reversal-bounded pushdown automata, and more generally of unambiguous nondeterministic Turing machines with a one-way input and a reversal-bounded worktape, are strongly counting-regular.

## Depends on

None.

## Proof depends on

None.

## Sources

- O. H. Ibarra, I. McQuillan and B. Ravikumar, "On counting functions and slenderness of languages", *Theoretical Computer Science* 777:356–378, 2019, doi:[10.1016/j.tcs.2018.11.021](https://doi.org/10.1016/j.tcs.2018.11.021); numbering of arXiv:1903.03504v1: the definitions of $f_L$, counting-regularity, strong counting-regularity, slenderness and boundedness in Section 2, and the examples and main positive results in Sections 1 and 3.
