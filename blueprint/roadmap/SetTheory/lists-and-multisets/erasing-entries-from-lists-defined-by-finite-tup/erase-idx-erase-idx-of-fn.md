# Ordered deletion of two tuple entries

For `v : Fin (n + 2) → α` and `i,j : Fin (n + 1)` with `i ≤ j`, delete
original position `j.val + 1` and then position `i.val`. The resulting list
is `List.ofFn (j.removeNth (i.castSucc.removeNth v))`; the latter removes `i`
first and then the shifted higher position `j` from the shortened tuple.
