# Subdividing the edges of a bandwidth instance

For an instance $(n,E,K)$ and a list $s$ of subdivision counts, the result is $(n+\sum s,E',K)$. Pair edges and counts in order until either list ends, starting with label $f=n$. For each paired edge $(a,b)$ and count $m>0$, append to $E'$ the consecutive pairs along $a,f,\ldots,f+m-1,b$ and advance $f$ by $m$. A zero count appends $(a,b)$ unchanged.

If $s$ is shorter than $E$, the unpaired edges are omitted. If $s$ is longer, its unpaired counts still contribute to the vertex count but produce no edges. For a well-formed graph with one count per edge, this is the usual subdivision with fresh vertices.
