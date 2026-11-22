/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AffineSLV

set_option linter.unusedSectionVars false

namespace AffineBuildingSLV

variable (C : DVRContext)

attribute [local instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain

end AffineBuildingSLV
