# Any Self Loop C

Assume that equality on `V` is decidable.

Costed self-loop scan: the same `Bool` as
`block.any fun s => graph.hasEdge s s`, plus the adjacency-entry scans.
`List.any` stops at the first `true` state; `listMemC` stops at the first
matching entry.
