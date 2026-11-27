# Component machine

A component machine consists of a finite type $K$ of stacks with
decidable equality, a finite alphabet $\Gamma_k$ for each stack $k$, a finite type $L$ of labels
with decidable equality, a multi-stack Turing machine program assigning to each label in $L$ a
statement over the alphabets $\Gamma$ and the labels $L$ with Boolean internal state, and a list
of the stacks in which every stack occurs exactly once, so that a host can empty all of them.
