# END-OF-THE-LINE is total

Let $V$ be a finite set, let $S, P : V \to V$ be maps and let $o \in V$ be a standard vertex with
$P(o) = o$ and $S(o) \neq o$ (so $o$ has no incoming edge in the
[END-OF-THE-LINE graph](adj.md), as $S(P(o)) = S(o) \neq o$). Then some $x \in V$ satisfies
$P(S(x)) \neq x$ (a sink) or $S(P(x)) \neq x$ with $x \neq o$ (a source other than $o$).

This is the existence statement behind the definition of END-OF-THE-LINE and of PPAD in
Constantinos Daskalakis, Paul W. Goldberg and Christos H. Papadimitriou, "The complexity of
computing a Nash equilibrium", SIAM J. Comput. 39(1) (2009), 195–259, where
$V = \{0,1\}^n$ and $o = 0^n$. In fact the first alternative always occurs
([Every END-OF-THE-LINE instance has a sink](exists-sink.md)).

## Informally uses

- [Every END-OF-THE-LINE instance has a sink](exists-sink.md): the first alternative always holds.
