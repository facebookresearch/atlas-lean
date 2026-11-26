# UNSAFE LOCKING POLICY is NP-complete

The UNSAFE LOCKING POLICY decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a finite list of transactions $T_0, \dots, T_{n-1}$ over variables that are natural numbers, each a sequence of steps of the forms $\mathrm{lock}(x)$, $\mathrm{update}(x)$ and $\mathrm{unlock}(x)$, such that for each variable $x$, the transaction either has no step on $x$, or has exactly one $\mathrm{lock}(x)$ and exactly one $\mathrm{unlock}(x)$, the $\mathrm{lock}(x)$ before the $\mathrm{unlock}(x)$, with every $\mathrm{update}(x)$ of the transaction (there may be any number of them, including none) strictly between the two. In particular a lone $\mathrm{unlock}(x)$, a lone $\mathrm{lock}(x)$, an $\mathrm{update}(x)$ without its $\mathrm{lock}(x)$-$\mathrm{unlock}(x)$ pair, and a second pair on the same variable are all excluded. Question: is there a legal schedule of the transactions that is not serializable, that is, an interleaving $S$ of all their steps, keeping the order of each transaction, such that between any two occurrences of $\mathrm{lock}(x)$ in $S$ (for any $x$) there is an occurrence of $\mathrm{unlock}(x)$, and such that the reads and writes of $S$ (each $\mathrm{update}(x)$ read as a read of $x$ followed by a write of $x$) do not leave the same final value of every variable as some serial execution of the transactions in some order, each write being read as an uninterpreted function of the values its transaction has read so far?

## Sources

- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300, doi:10.1016/0196-6774(83)90028-7, problem [6] UNSAFE LOCKING POLICY (reference: Papadimitriou and Yannakakis; transformation from 3SAT), and Section 3 (serializability).
- C. H. Papadimitriou, "Concurrency control by locking", SIAM J. Comput. 12 (1983), 215-226, doi:10.1137/0212013.
- M. Yannakakis, "A theory of safe locking policies in database systems", J. ACM 29 (1982), 718-740, doi:10.1145/322326.322333.
