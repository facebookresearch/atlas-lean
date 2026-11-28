# Emptiness of class automata on data words is undecidable

A class automaton relabels a data word by a letter-to-letter transducer and requires a regular condition to hold for every data class together with its context; no algorithm decides whether such an automaton accepts any data word, while the restricted data automata have decidable emptiness.

A *data word* over a finite alphabet $\Sigma$ is a word $w\in\Sigma^*$ with an equivalence relation $\sim$ on its positions, whose classes stand for positions carrying equal data values (data trees are defined in the same way). A *class automaton* is given by an input alphabet $\Sigma$, a work alphabet $\Gamma$, a nondeterministic letter-to-letter transducer $f$ from $\Sigma$ to $\Gamma$, and a regular *class condition* $L\subseteq(\Gamma\times\{0,1\})^*$. It accepts $(w,\sim)$ if some output $v\in f(w)$ satisfies $v\otimes X\in L$ for every class $X$, where $v\otimes X$ marks the positions of $X$ by $1$ and all others by $0$. A *data automaton* is the special case where the condition may only inspect the positions of the class: it is a language over $\Gamma$ applied to the subsequence $v|_X$.

**Theorem (Bojańczyk and Lasota).** Emptiness of class automata on data words, and hence on data trees, is undecidable.

The source gives two reasons: class automata capture every unary XPath query over data trees (Theorem 1 of arXiv:1201.0597v2), and XPath satisfiability is undecidable already on data words; and runs of two-counter machines can be encoded directly.

By contrast, emptiness is decidable for data automata (Bojańczyk, David, Muscholl, Schwentick and Segoufin) and for class automata with Wu's *priority* class condition, which corresponds to priority multicounter automata (Wu).

## Depends on

- [Register automata on data words](../../../regular-languages/register-automata-on-data-words/register-automata-on-data-words.md)
- [Rational relations and transducers](../../../regular-languages/automata-and-expressions/rational-relations-and-transductions/rational-relations-and-transducers.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Both sources note that emptiness can be shown undecidable directly by encoding runs of two-counter machines in data words, since the class condition sees the whole relabeled word around each marked class; neither writes the encoding out. The route given in detail is the main theorem of Bojańczyk and Lasota, which translates every unary XPath query over data trees into a class automaton, combined with the undecidability of XPath satisfiability over data words (Benedikt, Fan and Geerts).

## Sources

- Mikołaj Bojańczyk and Sławomir Lasota, "An extension of data automata that captures XPath", *Logical Methods in Computer Science* 8(1), 2012, paper 5, doi:[10.2168/LMCS-8(1:5)2012](https://doi.org/10.2168/LMCS-8(1:5)2012); read in arXiv:1201.0597v2 ([arXiv](https://arxiv.org/abs/1201.0597v2)): Section 3 (the definition of class automata, the paragraph "Comparison to data automata", which states the undecidability of emptiness, and Theorem 1) and the introduction.
- Zhilin Wu, "A Decidable Extension of Data Automata", in *Proceedings of GandALF 2011*, Electronic Proceedings in Theoretical Computer Science 54, 2011, pp. 116–130, doi:[10.4204/EPTCS.54.9](https://doi.org/10.4204/EPTCS.54.9); read in arXiv:1106.1235v1 ([arXiv](https://arxiv.org/abs/1106.1235v1)): the abstract and introduction (undecidability of class automata, the priority class condition).
