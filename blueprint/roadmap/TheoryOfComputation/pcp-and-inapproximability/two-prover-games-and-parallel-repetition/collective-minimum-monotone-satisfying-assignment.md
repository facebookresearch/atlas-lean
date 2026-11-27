# Collective Minimum Monotone Satisfying Assignment (CMMSA)

An instance of *CMMSA* consists of a set of Boolean variables $x_1, \dots, x_N$ with nonnegative integer weights $w_i$, a list of monotone formulas $\varphi_1, \dots, \varphi_m$ in disjunctive normal form over these variables, and a threshold $\theta$. A *satisfying assignment* is a set $S$ of variables that makes every $\varphi_j$ true; its weight is $\sum_{i \in S} w_i$. The gap problem $\mathrm{GapCMMSA}_g$ asks to distinguish instances having a satisfying assignment of weight at most $\theta$ from instances in which every satisfying assignment has weight greater than $g\theta$. Bounded-occurrence variants additionally bound the number of terms per formula and the term width by a parameter $\Delta$.

## Sources

- S. Hirahara, "NP-Hardness of Learning Programs and Partial MCSP", FOCS 2022.
- G. Kortsarz, "On the Hardness of Approximating Spanners", Algorithmica 30(3), 2001.
