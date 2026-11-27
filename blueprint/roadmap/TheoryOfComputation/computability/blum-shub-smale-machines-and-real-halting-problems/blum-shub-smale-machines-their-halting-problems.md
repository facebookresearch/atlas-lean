# Blum-Shub-Smale machines, their halting problems and analytic machines

A Blum-Shub-Smale machine computes over the real numbers with exact arithmetic and comparisons; its halting problem, iterated through
oracles, gives a hierarchy of real halting problems, against which problems about analytic machines, which output infinite sequences of
approximations, are classified.

**BSS machines.** A *Blum-Shub-Smale (BSS) machine* over $\mathbb{R}$ is a program with a countable sequence of real registers, accessed
directly or by indirect addressing through integer index registers, that performs the operations $+, -, \times, \div$, branches on the tests
$=$ and $<$, copies registers and initializes them to finitely many real constants of the program. It takes an input
$\vec x \in \mathbb{R}^* = \bigcup_d \mathbb{R}^d$ in its registers, with the dimension $d$ in an index register, and, if it halts, outputs the contents of its
real registers up to the index given by an index register. A set $S \subseteq \mathbb{R}^*$ is *BSS-decidable* if some BSS machine reports in finite time
whether $\vec x \in S$, and *BSS-semidecidable* if some BSS machine halts exactly on the inputs in $S$. Oracle BSS machines may in addition ask whether
a vector lies in a fixed oracle set. A set $S$ is *BSS many-one reducible* to $T$, written $S \preceq T$, if $S = f^{-1}(T)$ for some BSS-computable total
function $f : \mathbb{R}^* \to \mathbb{R}^*$.

**Real halting problems.** Machines are encoded by finite real vectors $\langle \mathcal{M} \rangle$, recording the program and its real constants. The *BSS
halting problem* is

$$
\mathbb{H} = \{(\langle \mathcal{M} \rangle, \vec x) : \text{the BSS machine } \mathcal{M} \text{ halts on input } \vec x\},
$$

and its iterates are $\mathbb{H}^{\mathbb{H}}$, the set of $(\langle \mathcal{M} \rangle, \vec x)$ such that the oracle BSS machine $\mathcal{M}^{\mathbb{H}}$ halts on $\vec x$, and likewise
$\mathbb{H}^{\mathbb{H}^{\mathbb{H}}}$ with oracle $\mathbb{H}^{\mathbb{H}}$. A set is semidecidable by a BSS machine with oracle $\mathbb{H}$ exactly when it is BSS many-one reducible to $\mathbb{H}^{\mathbb{H}}$
(Cucker).

**Analytic machines.** An *analytic machine* is a BSS machine that, instead of halting, prints an infinite sequence $(\vec y_n)_n$ of vectors. It
computes $f(\vec x)$ *strongly* if $\dim \vec y_n = \dim f(\vec x)$ and $\|\vec y_n - f(\vec x)\|_1 \le 2^{-n}$ for all $n$, and *weakly* if the dimensions agree from some $n$ on
and $\vec y_n \to f(\vec x)$. Two decision problems about analytic machines are the *boundedness problem*

$$
\mathbb{B} = \{(\langle \mathcal{M} \rangle, \vec x) : \mathcal{M} \text{ on input } \vec x \text{ produces a bounded sequence}\},
$$

where a finite output sequence counts as bounded, and the *convergence problem*

$$
\mathbb{K} = \{(\langle \mathcal{M} \rangle, \vec x) : \mathcal{M} \text{ on input } \vec x \text{ produces a convergent infinite sequence}\}.
$$

## Depends on

None.

## Proof depends on

None.

## Sources

- T. Gärtner and M. Ziegler, "Real analytic machines and degrees", *Logical Methods in Computer Science* 7(3), paper 11, 2011, doi:10.2168/LMCS-7(3:11)2011; read in arXiv:1006.0398v3: Section 1.4 (BSS machines and Definition 1.2), Section 1.5 (the arithmetical hierarchy for BSS machines, Fact 1.3, with the iterated halting problem), Section 1.6 (analytic machines), the definition of $\mathbb{B}$ in Section 3.1 and Definition 3.10 ($\mathbb{K}$).
