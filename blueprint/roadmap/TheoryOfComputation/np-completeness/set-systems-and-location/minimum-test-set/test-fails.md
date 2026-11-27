# Test Fails

The test $p = (u, v)$ fails when the link $(a, b)$ fails: $u$ reaches $a$ and $b$ reaches $v$. This does not test that $a \to b$ is an arc; for a link of the well-formed directed acyclic graph, which is an arc, the condition says that the link lies on a directed path from $u$ to $v$.
