# Karp's SAT-to-CLIQUE map on bit strings

The map on bit strings that decodes its input as
a CNF formula $\varphi$ (rejecting missing or trailing bits) and returns Karp's CLIQUE instance of
$\varphi$; an input that does not decode is sent to the fixed no-instance $k = 1$ on the graph
with no vertices.
