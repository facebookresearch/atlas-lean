# Array folds logic

Array folds logic extends the quantifier-free theory of integer arrays with fold terms, which run a small counter program over an array element by element and return the final counter values.

*Array folds logic* (AFL) has sorts for arrays of integers, integers, Booleans, integer vectors of each length $m\ge1$, and *functional constants* of sort $\mathbb Z^m\times\mathbb Z\to\mathbb Z^m$. Array terms are array variables $a$ and writes $a\{T\leftarrow T\}$; integer terms are constants $n\in\mathbb Z$, variables, sums, reads $a[T]$ and lengths $|a|$; Boolean terms are array equalities, linear comparisons $T=T$, $T<T$, Boolean combinations and equalities $V^m=V^m$ of vector terms. A vector term is a tuple of integer terms or a *fold* $\mathsf{fold}_a\,v\,f$, where $f$ is a list of guarded commands $\gamma\Rightarrow\upsilon$ over the implicit variables $\mathsf{elem}$ (current element), $\mathsf{idx}$ (current index), counters $\mathsf{cnt}_1,\dots,\mathsf{cnt}_{m-1}$ and a finite-state control variable $\mathsf{st}$. Guards compare these variables with integer terms; updates add constants to counters, set $\mathsf{st}$ to a constant, do nothing, or $\mathsf{break}$. Guards of the branches are mutually exclusive, a missing case breaks, and in every strongly connected component of the control-flow graph of $\mathsf{st}$ each counter changes monotonically.

The fold starts from the vector $v$ (initial index and counters) and applies $f$ to successive elements, incrementing $\mathsf{idx}$, until the index leaves $[0,|a|)$ or $\mathsf{break}$ fires; its value is the final vector. An interpretation assigns integers to integer variables and finite integer sequences to array variables; free variables are existentially quantified, and *satisfiability* asks for a satisfying interpretation.

## Depends on

None.

## Proof depends on

None.

## Expansion

Folds express counting properties of arrays, such as that an array holds exactly as many zeros as ones, which are beyond the quantifier-free theory of arrays. Satisfiability of AFL is PSPACE-complete, and NP-complete under a natural restriction (the source's main results).

## Sources

- Przemysław Daca, Thomas A. Henzinger and Andrey Kupriyanov, "Array Folds Logic", in *Computer Aided Verification (CAV 2016)*, Lecture Notes in Computer Science, Springer, 2016, pp. 230–248, doi:[10.1007/978-3-319-41540-6_13](https://doi.org/10.1007/978-3-319-41540-6_13); read in arXiv:1603.06850v3 ([arXiv](https://arxiv.org/abs/1603.06850v3)), whose numbering is used: Sections 2.1 and 2.2 (syntax and semantics of AFL, Tables 1 and 2), Theorem 1 (PSPACE-completeness) in Section 4 and Lemma 2 (NP-completeness of $m$-AFL) in Section 5.
