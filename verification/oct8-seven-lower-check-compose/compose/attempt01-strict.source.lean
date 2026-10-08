import Jsp000404.SevenLowerReplay

set_option autoImplicit false
set_option pp.fullNames true

/-! SOURCE_ONLY exact compositional checks for the frozen fixed-m6 DAG.
Each helper only unfolds the original checker one step. All child checks
keep the actual setter-chain context and remaining fuel. No model premise,
solver result, dropped branch or replacement root goal is introduced.
-/

namespace Jsp404.SevenLowerCheckCompose

open SevenLowerReplay

theorem check_leaf_of_cycle (nodes : NodeLibrary) (cycles : CycleLibrary)
    (fuel : ℕ) (ctx : Context) (id cid : ℕ)
    (hnode : nodes id = some (.leaf cid))
    (hcycle : cycleLibraryCheck cycles ctx cid = true) :
    check nodes cycles (fuel + 1) ctx id = true := by
  simpa only [check, hnode] using hcycle

theorem check_triangle_of_children (nodes : NodeLibrary) (cycles : CycleLibrary)
    (fuel : ℕ) (ctx : Context) (id : ℕ) (t : Fin 20) (lo hi : ℕ)
    (hnode : nodes id = some (.triangle t lo hi)) (hslot : ctx.tri t = none)
    (hlo : check nodes cycles fuel (setTriangle ctx t false) lo = true)
    (hhi : check nodes cycles fuel (setTriangle ctx t true) hi = true) :
    check nodes cycles (fuel + 1) ctx id = true := by
  simpa only [check, hnode, hslot, ↓reduceIte, Bool.and_eq_true] using And.intro hlo hhi

theorem check_heavy_of_children (nodes : NodeLibrary) (cycles : CycleLibrary)
    (fuel : ℕ) (ctx : Context) (id : ℕ) (children : Fin 21 → ℕ)
    (hnode : nodes id = some (.heavy children)) (hslot : ctx.heavy = none)
    (hchildren : ∀ p : Fin 21, check nodes cycles fuel (setHeavy ctx p) (children p) = true) :
    check nodes cycles (fuel + 1) ctx id = true := by
  simp only [check, hnode, hslot, ↓reduceIte]
  exact decide_eq_true hchildren

theorem check_positive_of_children (nodes : NodeLibrary) (cycles : CycleLibrary)
    (fuel : ℕ) (ctx : Context) (id : ℕ) (j : Fin 4) (children : Fin 6 → ℕ)
    (hnode : nodes id = some (.positive j children)) (hslot : ctx.positive j = none)
    (hchildren : ∀ t : Fin 6, check nodes cycles fuel (setPositive ctx j t) (children t) = true) :
    check nodes cycles (fuel + 1) ctx id = true := by
  simp only [check, hnode, hslot, ↓reduceIte]
  exact decide_eq_true hchildren

#print axioms check_leaf_of_cycle
#print axioms check_triangle_of_children
#print axioms check_heavy_of_children
#print axioms check_positive_of_children

end Jsp404.SevenLowerCheckCompose
