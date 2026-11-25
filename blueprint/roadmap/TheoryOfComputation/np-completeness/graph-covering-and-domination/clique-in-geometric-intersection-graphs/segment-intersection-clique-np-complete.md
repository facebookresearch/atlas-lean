# CLIQUE in segment intersection graphs (SEG) is NP-complete

The CLIQUE in segment intersection graphs (SEG) decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a finite set of straight line segments in the plane, each given by the integer coordinates of its two (distinct) endpoints, and a positive integer `K` at most the number of segments. Question: does the intersection graph of the segments (one vertex per segment, two segments adjacent when they share a point) contain a clique of size `K` or more?

## Sources

- S. Cabello, J. Cardinal and S. Langerman, "The clique problem in ray intersection graphs", Discrete & Computational Geometry 50 (2013), 771-783, doi:10.1007/s00454-013-9538-5 (arXiv:1111.5986).
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE.
- ISGCI (https://www.graphclasses.org/classes/gc_862.html), problem "Clique" on SEG graphs: NP-complete, with the attribution to Cabello, Cardinal and Langerman.
