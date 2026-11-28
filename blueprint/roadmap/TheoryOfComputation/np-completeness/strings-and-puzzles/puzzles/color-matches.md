# Color matches of a guess

For a code $s = (s_0, \dots, s_{\ell - 1})$ of colors below $\kappa$ and a guess $g$, the number of color matches irrespective of position is

$$\sum_{j < \kappa} \min\big(\#\{i < \ell : g_i = j\},\ \#\{i < \ell : s_i = j\}\big),$$

where both counts run over the first $\ell$ positions and positions beyond the end of $g$ read as color $0$. Entries of $g$ at positions $\ge \ell$ are ignored: the code $[1]$ and the guess $[0, 1]$ have $0$ color matches.
