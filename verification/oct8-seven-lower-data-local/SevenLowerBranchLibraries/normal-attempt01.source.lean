import Jsp000404.SevenLowerBranchShard00
import Jsp000404.SevenLowerBranchShard01
import Jsp000404.SevenLowerBranchShard02
import Jsp000404.SevenLowerBranchShard03
import Jsp000404.SevenLowerBranchShard04
import Jsp000404.SevenLowerBranchShard05
import Jsp000404.SevenLowerBranchShard06
import Jsp000404.SevenLowerBranchShard07

/-! SOURCE_ONLY literal certificate data; no kernel PASS is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerBranchLibraries
open SevenLowerReplay
def cycles (id : ℕ) : Option Cycle :=
  match id / 1024 with
  | 0 => SevenLowerBranchShard00.cycles (id % 1024)
  | 1 => SevenLowerBranchShard01.cycles (id % 1024)
  | 2 => SevenLowerBranchShard02.cycles (id % 1024)
  | 3 => SevenLowerBranchShard03.cycles (id % 1024)
  | 4 => SevenLowerBranchShard04.cycles (id % 1024)
  | 5 => SevenLowerBranchShard05.cycles (id % 1024)
  | 6 => SevenLowerBranchShard06.cycles (id % 1024)
  | 7 => SevenLowerBranchShard07.cycles (id % 1024)
  | _ => none

def nodes (id : ℕ) : Option Node :=
  match id / 1536 with
  | 0 => SevenLowerBranchShard00.nodes (id % 1536)
  | 1 => SevenLowerBranchShard01.nodes (id % 1536)
  | 2 => SevenLowerBranchShard02.nodes (id % 1536)
  | 3 => SevenLowerBranchShard03.nodes (id % 1536)
  | 4 => SevenLowerBranchShard04.nodes (id % 1536)
  | 5 => SevenLowerBranchShard05.nodes (id % 1536)
  | 6 => SevenLowerBranchShard06.nodes (id % 1536)
  | 7 => SevenLowerBranchShard07.nodes (id % 1536)
  | _ => none

end Jsp404.SevenLowerBranchLibraries
