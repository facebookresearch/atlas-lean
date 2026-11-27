# Binarization of a grammar

Let $g$ be a context-free grammar with nonterminals $N$ and
initial nonterminal $S$, and let $t_0, \dots, t_{k-1}$ be the list of terminals occurring in the
production outputs of $g$. Encode each symbol of a production output of $g$ as a basic symbol in
$N \sqcup \mathbb{N}$: a nonterminal $A$ as $A$, and a terminal $a$ as the least index $i$ with
$t_i = a$. The binarized grammar of $g$ has as nonterminals the basic symbols together with a
chain nonterminal $\langle\tau\rangle$ for every list $\tau$ of basic symbols, and its initial
nonterminal is $S$. For a list $\sigma$ of basic symbols, its head $h(\sigma)$ is defined by
$h(XY) = XY$ and $h(XYZ\tau) = X\langle YZ\tau\rangle$ for basic symbols $X, Y, Z$ and a list
$\tau$, $h(i) = t_i$ for a single index $i < k$, and $h(\sigma)$ empty in every other case. For
every production $A \to \alpha$ of $g$, with $\sigma$ the encoding of $\alpha$ symbol by symbol,
the binarized grammar has the production $A \to h(\sigma)$, the production
$\langle\tau\rangle \to h(\tau)$ for every suffix $\tau$ of $\sigma$ (including $\sigma$ itself)
with at least two entries, and the production $i \to a$ for every terminal $a$ occurring in
$\alpha$, where $i$ is the encoding of $a$; it has no other productions.

This construction is meant for reduced grammars, which have no empty outputs and no outputs
consisting of a single nonterminal: on other grammars such outputs get the empty head, and in
general neither the language nor Chomsky normal form is preserved.
