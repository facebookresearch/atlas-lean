# CHAMBERLIN-COURANT WINNER DETERMINATION is NP-complete

The decision problem CHAMBERLIN-COURANT WINNER DETERMINATION belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

## Sources

- T. Lu and C. Boutilier, "Budgeted social choice: From consensus to personalized decision making", Proceedings of the 22nd International Joint Conference on Artificial Intelligence (IJCAI 2011), 280-286, https://www.ijcai.org/Proceedings/11/Papers/057.pdf, Theorem 8 (stated for the Borda score `∑ᵥ maxₐ (m - 1 - posᵥ(a)) ≥ t`, which for $t \le n(m - 1)$ is the bound $B = n(m - 1) - t$ on the misrepresentation below; a threshold $t > n(m - 1)$ can never be met and is mapped to a fixed no-instance, since $B$ is a natural number).
- N. Betzler, A. Slinko, and J. Uhlmann, "On the computation of fully proportional representation", Journal of Artificial Intelligence Research 47 (2013), 475-519, doi:10.1613/jair.3896, Theorem 2.
