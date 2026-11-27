# One coded URM step

A coded state is a program counter $k$ together with a list $r$ of
register contents (in use, the contents of registers $0, \dots, R$, where $R$ is the register bound
of the program), and a program is given by the list $c$ of its instruction codes. Write $c_k$ for
entry $k$ of $c$, and $r_j$ for entry $j$ of $r$, read as $0$ when $j$ is past the end of $r$;
setting an entry past the end of $r$ leaves $r$ unchanged. If $k$ is at least the length of $c$,
the state is halted and has no successor. Otherwise unpair the code $c_k$ as $(i, a)$. If
$i = 0$, the successor is $(k + 1, r')$ where $r'$ is $r$ with entry $a$ set to $0$. If $i = 1$,
it is $(k + 1, r')$ where $r'$ is $r$ with entry $a$ set to $r_a + 1$. If $i = 2$, unpair $a$ as
$(m, n)$; the successor is $(k + 1, r')$ where $r'$ is $r$ with entry $n$ set to $r_m$. If
$i = 3$, unpair $a$ as $(m, b)$ and $b$ as $(n, q)$; the successor is $(q, r)$ if $r_m = r_n$ and
$(k + 1, r)$ otherwise. Any other tag $i$ (which never occurs for a genuine instruction code)
gives no successor.
