# SHORTEST COMMON SUPERSTRING is NP-complete

Instance: an alphabet $\{0, \dots, k - 1\}$, a finite list $R$ of strings over it, and a positive integer $K$. Question: is there a string $w$ over the alphabet with $|w| \le K$ that contains every $x \in R$ as a contiguous substring? This decision problem, with instances encoded as bitstrings and malformed or undecodable inputs as no-instances, is in NP, and every NP language reduces to it by a polynomial-time many-one reduction.

## Sources

M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman, 1979, problem [SR9].

J. Gallant, D. Maier and J. A. Storer, "On finding minimal length superstrings", *Journal of Computer and System Sciences* 20 (1980), 50-58.
