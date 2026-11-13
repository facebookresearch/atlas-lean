# Step count of the verifier's main scan

The number $T(r, bs, as, fl) \in \mathbb{N}$, for
bit strings $r$, $bs$, $as$ and a flag $fl$, is defined by recursion on $r$, where $0$ is false
and $1$ is true, juxtaposition denotes concatenation (so $b\,r$ is $r$ with the bit $b$
prepended), $[\,]$ is the empty string, $\mathrm{rev}$ reverses a string and $|\cdot|$ is length:

* $T(0\,0\,r, bs, as, fl) = |as| + 3 + T(r, \mathrm{rev}(as)\,bs, [\,], \mathrm{false})$ if $fl$
  is true, and $|as| + 3 + (|r| + (|as| + |bs|) + 3)$ otherwise;
* $T(0\,1\,r, [\,], as, fl) = 3 + T(r, [\,], as, fl)$;
* $T(0\,1\,r, x\,bs, as, fl) = 3 + T(r, bs, x\,as, fl)$;
* $T(1\,s\,r, [\,], as, fl) = 3 + T(r, [\,], as, fl)$;
* $T(1\,s\,r, x\,bs, as, fl) = 3 + T(r, bs, x\,as, fl \lor (x = \lnot s))$;
* $T(r, bs, as, fl) = |r| + |as| + |bs| + 4$ when $r$ has fewer than two bits.

The recursion mirrors the dense CNF evaluation scan.
