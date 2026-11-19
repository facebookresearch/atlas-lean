# Run of the subset-sum emitter's pair walk

Let $L_m \ne []$, $r_m$ and $w$ be lists of
booleans, and for a list $\ell$ of booleans write $\bar\ell$ for the list of mark symbols
$\mathrm{val}(x)$, $x \in \ell$. Let $(a_1, c_1), \dots, (a_m, c_m)$ be the mark pairs
$\mathrm{walkM}(L_m, r_m)$, and suppose $w = (b_1, \dots, b_m)$ has the same length $m$. Start the
emitter machine at label $\mathrm{pr}$ with any internal state $v$ and stacks $S$ such that
$S_L = \bar L_m$, $S_R = \bar r_m$, $S_{Rt}$ is empty and $S_Y = \bar w \mathbin{+\!\!+} y$ for a
list of symbols $y$. Then after exactly $2m + 3|L_m|$ steps the machine is at label
$\mathrm{vend}$, with some internal state $v'$ and stacks $S'$ such that $S'_L$ and $S'_{Rt}$ are
empty, $S'_R = \overline{\mathrm{rev}(L_m) \mathbin{+\!\!+} r_m}$, $S'_Y = y$,
$S'_Z = \mathrm{rev}(\bar w) \mathbin{+\!\!+} S_Z$ and $S'_O = \mathrm{blk}(t_m) \mathbin{+\!\!+}
\cdots \mathbin{+\!\!+} \mathrm{blk}(t_1) \mathbin{+\!\!+} S_O$,
where $t_i = b_i \wedge (c_i \vee a_i)$ and $\mathrm{blk}(t) = [\mathrm{true}, t, \mathrm{true},
\mathrm{false}]$; every stack other than $L$, $R$, $Rt$, $Y$, $Z$ and $O$ is unchanged.

The rows of the walk come from the vertex marks on $L$ (top first) and the columns from the marks
on $R$; after each row the column marks are restored from $Rt$ and the row mark moves onto $R$.
