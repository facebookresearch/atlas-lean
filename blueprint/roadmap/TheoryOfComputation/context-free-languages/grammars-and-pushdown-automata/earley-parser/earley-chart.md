# Earley chart

Let $G$ be a context-free grammar with terminals $T$ and initial nonterminal $S$, and let $w$ be a word over $T$.
The Earley chart of $G$ on $w$ is the least relation $E(r, k, p, c)$ between productions $r$ of $G$, dot
positions $k \in \mathbb{N}$ and words $p, c$ over $T$ closed under the following rules, where $\gamma_k$ denotes
the symbol at position $k$ (counting from $0$) of the right side $\gamma$ of $r$, when it exists:

- initialization: $E(r, 0, \varepsilon, \varepsilon)$ for every production $r$ of $G$ with left side $S$;
- prediction: if $E(r, k, p, c)$ and $\gamma_k$ is a nonterminal $A$, then $E(r', 0, pc, \varepsilon)$ for every
  production $r'$ of $G$ with left side $A$;
- scanning: if $E(r, k, p, c)$, $\gamma_k$ is a terminal $a$, and $w = p\,c\,a\,u$ for some word $u$, then
  $E(r, k + 1, p, ca)$;
- completion: if $E(r, k, p, c)$, $\gamma_k$ is a nonterminal $A$, $r'$ is a production of $G$ with left side
  $A$ and right side $\gamma'$, and $E(r', |\gamma'|, pc, c')$, then $E(r, k + 1, p, cc')$.

## Sources

- J. Earley, "An efficient context-free parsing algorithm", *Communications of the ACM* 13 (1970), 94–102.
