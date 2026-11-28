# Counting-regular languages

The counting function of a language gives the number of its words of each length. A language is counting-regular if some regular language has the same counting function.

**Definition.** For a language $L \subseteq \Sigma^*$ let $f_L(n)$ be the number of words of length $n$ in $L$. The language $L$ is called

- *counting-regular* if there is a regular language $L'$ (over some alphabet) with $f_L(n) = f_{L'}(n)$ for all $n \ge 0$;
- *strongly counting-regular* if $L \cap L_1$ is counting-regular for every regular language $L_1$.

Every regular language is counting-regular, and so is, for example, $\{ww : w \in \{a, b\}^*\}$, which has as many words of each length as $(a(a+b))^*$. Languages of unambiguous reversal-bounded pushdown automata, and more generally of unambiguous nondeterministic Turing machines with a one-way input and a reversal-bounded worktape (one whose head changes direction a bounded number of times), are strongly counting-regular.

## Depends on

None.

## Proof depends on

None.

## Sources

- O. H. Ibarra, I. McQuillan and B. Ravikumar, "On counting functions and slenderness of languages", *Theoretical Computer Science* 777:356–378, 2019, doi:[10.1016/j.tcs.2018.11.021](https://doi.org/10.1016/j.tcs.2018.11.021); numbering of arXiv:1903.03504v1: the definitions of $f_L$, counting-regularity and strong counting-regularity in Section 2, and the examples and main positive results in Sections 1 and 3.
