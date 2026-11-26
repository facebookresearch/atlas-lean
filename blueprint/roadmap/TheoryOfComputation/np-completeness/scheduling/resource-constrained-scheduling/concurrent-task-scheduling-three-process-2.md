# CONCURRENT TASK SCHEDULING ON THREE PROCESSORS is NP-complete

The decision problem CONCURRENT TASK SCHEDULING ON THREE PROCESSORS belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- E. L. Lloyd, "Concurrent task systems", Operations Research 29 (1981), 189-201, doi:10.1287/opre.29.1.189 (abstract: a concurrent task system "consists of: m identical processors, tasks T₁, …, Tₙ, and a partial order on those tasks which represents precedence constraints. Associated with each task Tᵢ is a positive integral execution time τᵢ and a degree of concurrency qᵢ ∈ 𝒞 where 𝒞 ⊆ {1, …, m}. Task Tᵢ must execute for τᵢ steps and for each of those τᵢ steps it requires qᵢ processors. ... we show that scheduling concurrent UET task systems is NP-complete even if there are only three processors and each task has a degree of concurrency of either 1 or 2"; the full text was not available to us).
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problems [SS9] PRECEDENCE CONSTRAINED SCHEDULING (every degree `1`) and [SS10] RESOURCE CONSTRAINED SCHEDULING (the model with precedence used here).
