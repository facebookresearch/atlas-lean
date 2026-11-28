# Weights of vertex pairs

The weight of the pair $(u, v)$ in a weight matrix is entry $v$ of row $u$; a missing row or entry gives $0$.

STRONG CONNECTIVITY AUGMENTATION uses this same lookup, `(w.getD u []).getD v 0`; positions beyond the end of the lists read as `[]` and `0`.
