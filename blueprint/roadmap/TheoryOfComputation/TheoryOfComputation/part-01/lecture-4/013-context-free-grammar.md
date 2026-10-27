---
article_id: af_380e162607092d8405e141ff
declaration: abbrev
origin: cited
statement: formalized
lean: ContextFree.CFG
---

# Definition (Context Free Grammar)

A Context Free Grammar (CFG) $G$ is a 4-tuple $(V, \Sigma, R, S)$ where $V$ is a finite set of variables, $\Sigma$ is a finite set of terminal symbols, $R$ is a finite set of rules (rule form $V \to (V \cup \Sigma)^*$), and $S$ is the start variable. For $u, v \in (V \cup \Sigma)^*$, write $u \Rightarrow v$ if one can go from $u$ to $v$ with one substitution step, and $u \Rightarrow^* v$ if one can go from $u$ to $v$ with some number of substitutions. $L(G) = \{w \mid w \in \Sigma^* \text{ and } S \Rightarrow^* w\}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 4, section on CFG — Formal Definition](../../../../../sources/v1/TheoryOfComputation.md)
