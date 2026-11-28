# Two Unit componentwise covariance

On a two-unit flux, toggling the copy of the second edge is a componentwise covariance for the
exhaustive program. Let `e ≠ f` be edges of the domain graph whose canonical segments are active
(`hactiveE`, `hactiveF`) and form a two-edge path (`hpath`), and suppose that the scan of the
two-edge program, which the exhaustive program shares, started at `d` with nothing accepted, admits
`e` first on the odd bits of `twoUnitFlux e f` (`hfirst`). Then toggling the labeled copy
`secondCopy` of `f` is a covariance (`BondwiseRunToggleCovariance`) on the sets of labeled copies of
`twoUnitFlux e f`: for every such set `T`, the profile of `T` completes the full run `[e, f]` of the
exhaustive program iff the profile of `T ∆ {secondCopy}` lies in the active-segment fibre of `e`,
and the profile of `T` lies in the residual vacuum after `e` iff the profile of `T ∆ {secondCopy}`
lies in the lifted residual run `[f]` of the exhaustive program.
