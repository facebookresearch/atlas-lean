/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

namespace Garrett

variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The restriction of a reflexive bilinear form to a subspace `U` is
nondegenerate iff `U` and its orthogonal complement form a direct sum. -/
theorem nondegenerate_iff_compl
    (B : LinearMap.BilinForm k V)
    (hBrefl : B.IsRefl)
    (U : Submodule k V) :
    (B.restrict U).Nondegenerate ↔ IsCompl U (LinearMap.BilinForm.orthogonal B U) :=
  B.restrict_nondegenerate_iff_isCompl_orthogonal hBrefl

/-- The restriction of `B` to `U` is nondegenerate iff its restriction to the
orthogonal complement `Uᗮ` is nondegenerate. -/
theorem nondegenerate_iff_orthogonal_nondegenerate
    (B : LinearMap.BilinForm k V)
    (hBnd : B.Nondegenerate)
    (hBrefl : B.IsRefl)
    (U : Submodule k V) :
    (B.restrict U).Nondegenerate ↔
    (B.restrict (LinearMap.BilinForm.orthogonal B U)).Nondegenerate := by
  constructor
  · intro hU

    have hcompl : IsCompl U (LinearMap.BilinForm.orthogonal B U) :=
      (B.restrict_nondegenerate_iff_isCompl_orthogonal hBrefl).mp hU

    have hdd : LinearMap.BilinForm.orthogonal B (LinearMap.BilinForm.orthogonal B U) = U :=
      LinearMap.BilinForm.orthogonal_orthogonal hBnd hBrefl U

    have hcompl' : IsCompl (LinearMap.BilinForm.orthogonal B U)
        (LinearMap.BilinForm.orthogonal B (LinearMap.BilinForm.orthogonal B U)) := by
      rw [hdd]; exact hcompl.symm

    exact (B.restrict_nondegenerate_iff_isCompl_orthogonal hBrefl).mpr hcompl'
  · intro hUperp

    have hcompl : IsCompl (LinearMap.BilinForm.orthogonal B U)
        (LinearMap.BilinForm.orthogonal B (LinearMap.BilinForm.orthogonal B U)) :=
      (B.restrict_nondegenerate_iff_isCompl_orthogonal hBrefl).mp hUperp

    have hdd : LinearMap.BilinForm.orthogonal B (LinearMap.BilinForm.orthogonal B U) = U :=
      LinearMap.BilinForm.orthogonal_orthogonal hBnd hBrefl U

    rw [hdd] at hcompl
    exact (B.restrict_nondegenerate_iff_isCompl_orthogonal hBrefl).mpr hcompl.symm

/-- `U` and `Uᗮ` form a direct sum iff the restriction of `B` to `Uᗮ` is
nondegenerate. -/
theorem compl_iff_orthogonal_nondegenerate
    (B : LinearMap.BilinForm k V)
    (hBnd : B.Nondegenerate)
    (hBrefl : B.IsRefl)
    (U : Submodule k V) :
    IsCompl U (LinearMap.BilinForm.orthogonal B U) ↔
    (B.restrict (LinearMap.BilinForm.orthogonal B U)).Nondegenerate :=
  (nondegenerate_iff_compl B hBrefl U).symm.trans
    (nondegenerate_iff_orthogonal_nondegenerate B hBnd hBrefl U)

end Garrett
