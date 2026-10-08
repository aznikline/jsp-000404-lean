import Jsp000404.SevenLowerBranchLibraries

/-! SOURCE_ONLY literal certificate data; no kernel PASS is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerBranchRootCheck
open SevenLowerReplay
theorem point_checked : check SevenLowerBranchLibraries.nodes SevenLowerBranchLibraries.cycles
    26 emptyContext 10813 = true := by decide

#print axioms point_checked
end Jsp404.SevenLowerBranchRootCheck
