# A vertex cover approximation below factor two yields a 3SAT decider

Fix a real $1\le\alpha<2$. Suppose one deterministic polynomial-time finite-stack machine with finite stack alphabets takes any finite simple unweighted graph to a list of distinct valid vertices meeting every edge, with list length at most $\alpha$ times the minimum cover size. The input representation uses framed binary vertex count, all vertex names, edge count and distinct increasing endpoint pairs; the list output is framed binary length followed by framed names. Then there is a deterministic polynomial-time finite-stack machine with finite stack alphabets that accepts precisely the raw words decoding to satisfiable three-slot CNFs. Both time bounds refer to their own original bit inputs. No assumption that $\mathsf P\ne\mathsf{NP}$ occurs in the implication.

## Depends on

- The finite-alphabet transducer for an explicit cover and the raw three-slot SAT language above.

## Proof depends on

- [Strict vertex cover density gaps from binary 3SAT](vertex-cover-strict-density-gap.md), with $m$ chosen so that $\alpha(1/2+1/m)\le1-1/m$.

## Expansion

Certify exact rational threshold comparison, chosen independently of the input, and composition on the actual graph and list encodings. Transport the feasibility and list length clauses, rather than treating an arbitrary objective-value estimate as an explicit cover algorithm.

## Sources

- OpenAI, [formula, encodings, approximation and decider](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/VertexCover.lean#L5-L150).
