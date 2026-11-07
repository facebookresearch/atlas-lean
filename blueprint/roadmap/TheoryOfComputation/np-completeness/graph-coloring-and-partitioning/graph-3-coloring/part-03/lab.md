# Control labels of the 3-coloring emitter

`init`: palette; `cls`: next clause; `lits`:
next literal; `lp`, `nm`: pop the polarity and the name; `walk` to `dr`: walk `D` (compare,
restore, select the polarity case, move the name and the vertex to `E`, or the vertex to `U`
and push the consistency edges); `back`: move `E` back to `D`; `putN` to `putP`: put the
occurrence on `D`; `aft`, `fA` to `fC`: set `R` and advance `N`; `clr`: clear `R`; `zN`:
advance `N` after an empty clause; `pre j`, `cpA j`, `cpB j`: copy site `j`; `done`: halt.
