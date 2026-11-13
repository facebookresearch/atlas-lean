/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Category.Basic

namespace AlgebraicTopologyI

/-- **Definition 3.1 (Category).**  A category, in the sense of Miller's
*Lectures on Algebraic Topology I*.  This is a thin wrapper around Mathlib's
`CategoryTheory.Category`, repackaging it under the `AlgebraicTopologyI`
namespace so that downstream files in this book can refer to it directly. -/
abbrev Category := @CategoryTheory.Category

end AlgebraicTopologyI
