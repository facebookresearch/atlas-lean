# Restoring and stashing after a comparison in the lookup machine

Let $q$, $n$, $c$ be
lists of bits such that $c$ is a prefix of both the reverse of $q$ and the reverse of $n$; let
$R$, $r$, $s$, $w$ be lists of symbols with $r$ empty or starting with a symbol other than a name
bit; and for a list of bits $x$ write $\bar x$ for the list of its bits as name bits. Suppose the
lookup program is at label $\mathsf{rstT}$, with any internal bit, and its stacks are: $T$ holds
the reverse of $\bar q$ with its first $|c|$ symbols removed, followed by $R$; $B$ holds the
reverse of $\bar n$ with its first $|c|$ symbols removed, followed by $r$; $S$ holds $s$; $A$ and
$C$ both hold the reverse of $\bar c$; and $V$ holds $w$. Then after exactly
$2(|c| + 1) + (|n| + 1)$ steps the program is at label $\mathsf{scan}$, with some internal bit,
where $T$ holds the reverse of $\bar q$ followed by $R$, $B$ holds $r$, $S$ holds $\bar n$
followed by $s$, $A$ and $C$ are empty, and $V$ holds $w$.
