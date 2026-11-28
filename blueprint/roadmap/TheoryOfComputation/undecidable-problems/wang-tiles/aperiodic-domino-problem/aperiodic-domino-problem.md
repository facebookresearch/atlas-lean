# The aperiodic domino problem

The aperiodic domino problem asks, given a family of forbidden patterns, whether the subshift it defines contains an aperiodic configuration; its variants restrict the input to subshifts of finite type or to sofic subshifts.

**Definition.** Let $\Sigma$ be a finite alphabet and $d \ge 1$, and use the notions of [subshifts of finite type, sofic and effective subshifts](subshifts-and-the-aperiodic-domino-problem.md), including aperiodic configurations. The *aperiodic domino problem* (AD) asks, given an effective family $\mathcal{F}$ of $d$-dimensional patterns (an instance is a Turing machine enumerating $\mathcal{F}$, each pattern given by its finite domain and its values), whether $X_{\mathcal{F}}$ contains an aperiodic configuration. Its variants restrict the input: for subshifts of finite type the input is a finite family $\mathcal{F}$, listed explicitly, and for sofic subshifts it is a finite family defining a subshift of finite type $X$ together with a letter-to-letter map $\pi$, the question being whether $\pi(X)$ contains an aperiodic configuration.

The source shows that the problem is in [$\Sigma^1_1$](analytical-class-sigma-1-1.md) for every $d$ (Proposition 10), since it asks for a configuration satisfying the arithmetical conditions "no pattern of $\mathcal{F}$ appears" and "every nonzero vector is broken", and that it is $\Pi^0_1$-hard for $d \ge 2$ (Proposition 9), by taking the product with a fixed subshift of finite type all of whose configurations are aperiodic.

## Depends on

- [Subshifts of finite type, sofic and effective subshifts](subshifts-and-the-aperiodic-domino-problem.md)

## Proof depends on

None.

## Sources

- A. Callard and B. Hellouin de Menibus, "The Aperiodic Domino Problem in Higher Dimension", *39th International Symposium on Theoretical Aspects of Computer Science (STACS 2022)*, Leibniz International Proceedings in Informatics 219, 2022, Article 19, doi:[10.4230/LIPIcs.STACS.2022.19](https://doi.org/10.4230/LIPIcs.STACS.2022.19); numbering of arXiv:2202.07377v1: Definition 8 (the problem AD), Proposition 9 ($\Pi^0_1$-hardness) and Proposition 10 (membership in $\Sigma^1_1$).
