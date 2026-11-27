# Visibly pushdown automata and visibly pushdown languages

A *pushdown alphabet* $\tilde\Sigma = \langle \Sigma_c, \Sigma_r, \Sigma_\ell \rangle$ splits a finite alphabet $\Sigma = \Sigma_c \cup \Sigma_r \cup \Sigma_\ell$ into disjoint sets of *calls*, *returns* and
*local actions*. A *visibly pushdown automaton* (VPA) over $\tilde\Sigma$ is a tuple $M = (Q, Q_{\mathrm{in}}, \Gamma, \delta, Q_F)$ with a finite set $Q$ of states, $Q_{\mathrm{in}}, Q_F \subseteq Q$, a finite stack alphabet $\Gamma$
containing a bottom symbol $\bot$ and
$\delta \subseteq (Q \times \Sigma_c \times Q \times (\Gamma \setminus \{\bot\})) \cup (Q \times \Sigma_r \times \Gamma \times Q) \cup (Q \times \Sigma_\ell \times Q)$: on a call it pushes one symbol, on a return
it pops one symbol (reading $\bot$ without popping it when the stack is empty), and on a local action it leaves the stack unchanged.
Runs start from an initial state with stack $\bot$, and a word is accepted if some run ends in a final state. A language is a *visibly
pushdown language* (VPL) with respect to $\tilde\Sigma$ if some VPA over $\tilde\Sigma$ accepts it. Every regular language over $\Sigma$ is a VPL for every
partition; with calls $\{a\}$ and returns $\{b\}$, $\{a^n b^n\}$ is a VPL while $\{b^n a^n\}$ is not, and the words with as many $a$'s as $b$'s form a
context-free language that is a VPL for no partition. VPAs are a restricted kind of [pushdown automaton](../grammars-and-pushdown-automata/pushdown-automata/pda.md), so
VPLs are context-free.

## Depends on

- [Pushdown automaton](../grammars-and-pushdown-automata/pushdown-automata/pda.md)

## Sources

- R. Alur and P. Madhusudan, "Visibly pushdown languages", *Proceedings of the 36th ACM STOC*, 2004; full version of August 2005, whose numbering is cited, <https://www.cis.upenn.edu/~alur/Stoc04.pdf>: Section 2.1, Definition 1 (visibly pushdown automaton), its runs and acceptance, Definition 2 (visibly pushdown languages) and the examples after it.
