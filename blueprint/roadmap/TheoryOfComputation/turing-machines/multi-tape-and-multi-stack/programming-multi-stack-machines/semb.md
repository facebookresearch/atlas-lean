# Stack embedding

Given a family of stack alphabets $\Gamma$ indexed by the stacks $K$ of a
sub-machine and a family $\Gamma'$ indexed by the stacks $K'$ of a host, a stack embedding
consists of an injective map $e : K \to K'$ renaming the stacks together with, for each stack
$k \in K$, a bijection $\iota_k : \Gamma_k \to \Gamma'_{e(k)}$ from the alphabet of $k$ onto the
alphabet of its image.
