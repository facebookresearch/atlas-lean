---
article_id: af_2395f80d833417fb4b41c0f9
declaration: structure
origin: cited
statement: formalized
lean: LogSpace.LogSpaceConfig
---

# Definition (Configuration for log-space TM)

A configuration for $M$ on $w$ is $(q, p_1, p_2, t)$ where $q$ is a state, $p_1$ and $p_2$ are the tape head positions, and $t$ is the tape contents. The number of such configurations is $|Q| \times n \times O(\log n) \times d^{O(\log n)} = O(n^k)$ for some $k$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.404J Theory of Computation (Fall 2020), Lecture 19, Log space properties](../../../../../sources/v1/TheoryOfComputation.md)
