# Context-sensitive grammar for $a^n b^n c^n$

The grammar $G_{abc}$ has terminals $a, b, c$, nonterminals $S, B, C$, initial nonterminal $S$, and the
seven productions

$$S \to aSBC,\quad S \to aBC,\quad CB \to BC,\quad aB \to ab,\quad bB \to bb,\quad bC \to bc,\quad cC \to cc.$$

It is the standard context-sensitive grammar for the language $\{a^n b^n c^n : n \ge 1\}$.
