# Records witness i-sequences

Let $b_k, \dots, b_0$ be the [record](i-sequences-and-records.md) obtained by reading a finite sequence of priorities $\pi$ from the all-$-$ record. If $b_i \ne -$
then $\pi$ contains an $i$-sequence; moreover the witnessed sequences satisfy the order property. Conversely, if $\pi$ is an infinite
sequence satisfying the max-parity condition, then for every $k$ some prefix of $\pi$ leads to a record with $b_k \ne -$: after the last
occurrence of a priority above the largest even priority $p$ seen infinitely often, each visit to $p$ triggers Step 1, and $2^k$ visits
set $b_k = p$.

## Depends on

- [i-sequences and records](i-sequences-and-records.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 2 (J. Fearnley and N. Fijalkow, "Parity games"): Section 2.4, Lemma 2.10 (correctness for the separating automaton) and Lemma 2.11 (weaker correctness) with their proofs.
