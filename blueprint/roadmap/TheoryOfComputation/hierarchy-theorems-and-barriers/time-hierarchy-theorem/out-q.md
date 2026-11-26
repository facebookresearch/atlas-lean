# Branch after comparing states

The label the checking machine goes to after comparing the
bound $p$ for the state (the state of the previous key, or $0$ at the first entry) with the
state $q$ of the current key: if $p < q$, the label $\mathsf{sk0}$, where it starts skipping the
rest of the entry; if $p = q$, the label $\mathsf{ca}$, where it compares the symbols; if
$p > q$, the label $\mathsf{bad}$, where it rejects.
