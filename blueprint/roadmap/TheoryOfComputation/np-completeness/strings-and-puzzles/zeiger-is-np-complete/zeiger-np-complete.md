# ZEIGER is NP-complete

Statement: the ZEIGER decision problem is NP-complete.

An instance is a rectangular grid in which every cell has an arrow pointing up, right, down or left, and some cells contain a positive integer. The question is whether a positive integer can be written in every unnumbered cell so that the integer in each cell equals the number of distinct integers in the cells strictly beyond it in the direction of its arrow, up to the edge of the grid. Instances are encoded as bitstrings; undecodable and malformed bitstrings are no-instances.

NP-completeness means both:

- the ZEIGER language is in NP;
- every language in NP has a polynomial-time many-one reduction to the ZEIGER language.

## Sources

- S. Ruangwises, "NP-completeness and physical zero-knowledge proofs for Zeiger", WALCOM: Algorithms and Computation, Lecture Notes in Computer Science (2025), 312–325, doi:10.1007/978-981-96-2845-2_20, arXiv:2409.14308.
