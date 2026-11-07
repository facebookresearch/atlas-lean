# Tail cells derive their activated encoding

The tail cells, sitting at offset `start ≥ 1` in a word of total length
`start + w.length`, derive their activated encoding. The offset stays
`≥ 1` in the induction step, so the first tail cell is never tagged
`left`: it is `right` when it is the last cell and `middle` otherwise.
