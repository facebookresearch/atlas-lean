# SIDE-CHAIN POSITIONING (PROTEIN DESIGN) is NP-complete

The SIDE-CHAIN POSITIONING (PROTEIN DESIGN) decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: positions $1, \dots, p$, each with a finite **nonempty** set $R_i$ of rotamers (the sets pairwise disjoint, every rotamer belonging to exactly one position); an integer self energy $E(r)$ for every rotamer $r$; an integer pairwise energy $E(r, s)$ for every ordered pair of rotamers; an integer $K$. Question: is there a choice of one rotamer $r_i \in R_i$ at each position $i$ whose total energy $\sum_i E(r_i) + \sum_i \sum_{j < i} E(r_i, r_j)$ is at most $K$?

## Sources

- N. A. Pierce and E. Winfree, "Protein design is NP-hard", Protein Engineering 15 (2002), 779-782, doi:10.1093/protein/15.10.779.
- B. Chazelle, C. Kingsford and M. Singh, "A semidefinite programming approach to side chain positioning with new rounding strategies", INFORMS Journal on Computing 16 (2004), 380-392, doi:10.1287/ijoc.1040.0096.
