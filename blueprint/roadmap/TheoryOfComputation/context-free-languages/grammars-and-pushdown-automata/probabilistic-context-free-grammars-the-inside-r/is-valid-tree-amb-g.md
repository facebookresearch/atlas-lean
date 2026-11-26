# Every derivation tree of the example grammar is valid

The ambiguous example grammar has one nonterminal $A$, which is its start symbol, one terminal $a$, and the two rules $A \to A\,A$ and $A \to a$. Every derivation tree whose labels are this grammar's nonterminal and terminal is valid for the grammar: its only possible leaf rule $A \to a$ and its only possible node rule $A \to A\,A$ are both rules of the grammar, and all roots are $A$.
