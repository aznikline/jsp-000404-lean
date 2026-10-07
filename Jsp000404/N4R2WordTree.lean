import Jsp000404.N4R2WordDefinitions
import Mathlib.Data.Fintype.Pi

/-! Complete finite packet-word coverage, with bounded ordinary-kernel checks.
Generated from the diagnostic catalog, never from a trusted solver premise.
No actual Model row or cycle soundness is assumed in this module.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
namespace Jsp404.N4R2WordTree

abbrev Word := N4R2WordDefinitions.Word
abbrev quadLabels := N4R2WordDefinitions.quadLabels
abbrev packetBits := N4R2WordDefinitions.packetBits
abbrev Partial := Fin 35 → Option Bool

def allowedPatterns : List (Fin 4 → Bool) := [
  ![false,false,false,false], ![false,false,false,true],
  ![false,false,true,true], ![false,true,true,true],
  ![true,false,false,false], ![true,true,false,false],
  ![true,true,true,false], ![true,true,true,true]]

def packetPattern (w : Word) (q : Fin 35) : Fin 4 → Bool :=
  fun k => w (packetBits q k)

def PacketValid (w : Word) : Prop :=
  ∀ q : Fin 35, packetPattern w q ∈ allowedPatterns

def Extends (w : Word) (p : Partial) : Prop :=
  ∀ i b, p i = some b → w i = b

def Compatible (p : Partial) (q : Fin 35) (v : Fin 4 → Bool) : Prop :=
  ∀ k b, p (packetBits q k) = some b → v k = b

instance (p : Partial) (q : Fin 35) (v : Fin 4 → Bool) :
    Decidable (Compatible p q v) :=
  inferInstanceAs (Decidable (∀ (k : Fin 4) (b : Bool),
    p (packetBits q k) = some b → v k = b))

def ForceValid (p : Partial) (q : Fin 35) (k : Fin 4) (b : Bool) : Prop :=
  ∀ v ∈ allowedPatterns, Compatible p q v → v k = b

instance (p : Partial) (q : Fin 35) (k : Fin 4) (b : Bool) :
    Decidable (ForceValid p q k b) :=
  inferInstanceAs (Decidable (∀ v : Fin 4 → Bool,
    v ∈ allowedPatterns → Compatible p q v → v k = b))

inductive Tree (n : ℕ) where
  | leaf (id : Fin n)
  | split (bit : Fin 35) (left right : Tree n)
  | force (packet : Fin 35) (localBit : Fin 4) (value : Bool) (next : Tree n)
  | dead (packet : Fin 35)

def check {n : ℕ} (catalog : Fin n → Word) (p : Partial) : Tree n → Bool
  | .leaf id => decide (∀ i : Fin 35, p i = some (catalog id i))
  | .split bit left right =>
      check catalog (Function.update p bit (some false)) left &&
      check catalog (Function.update p bit (some true)) right
  | .force q k b next => decide (ForceValid p q k b) &&
      check catalog (Function.update p (packetBits q k) (some b)) next
  | .dead q => decide (∀ v ∈ allowedPatterns, ¬ Compatible p q v)

theorem extends_update (w : Word) (p : Partial) (i : Fin 35) (b : Bool)
    (hp : Extends w p) (hb : w i = b) :
    Extends w (Function.update p i (some b)) := by
  intro j c hc
  by_cases hji : j = i
  · subst j
    have hbc : b = c := by simpa using hc
    exact hb.trans hbc
  · have hpc : p j = some c := by simpa [Function.update, hji] using hc
    exact hp j c hpc

theorem compatible_actual (w : Word) (p : Partial) (q : Fin 35)
    (hp : Extends w p) : Compatible p q (packetPattern w q) := by
  intro k b hb
  exact hp (packetBits q k) b hb

theorem check_complete {n : ℕ} (catalog : Fin n → Word) (t : Tree n) :
    ∀ p : Partial, check catalog p t = true →
    ∀ w : Word, PacketValid w → Extends w p → ∃ id, w = catalog id := by
  induction t with
  | leaf id =>
      intro p hc w hw hp
      have hfull : ∀ i : Fin 35, p i = some (catalog id i) := of_decide_eq_true hc
      exact ⟨id, funext (fun i => hp i (catalog id i) (hfull i))⟩
  | split bit left right ihleft ihright =>
      intro p hc w hw hp
      simp only [check, Bool.and_eq_true] at hc
      cases hb : w bit with
      | false => exact ihleft _ hc.1 w hw (extends_update w p bit false hp hb)
      | true => exact ihright _ hc.2 w hw (extends_update w p bit true hp hb)
  | force q k b next ih =>
      intro p hc w hw hp
      simp only [check, Bool.and_eq_true] at hc
      have hf : ForceValid p q k b := of_decide_eq_true hc.1
      have hb : w (packetBits q k) = b :=
        hf (packetPattern w q) (hw q) (compatible_actual w p q hp)
      exact ih _ hc.2 w hw (extends_update w p (packetBits q k) b hp hb)
  | dead q =>
      intro p hc w hw hp
      have hd : ∀ v ∈ allowedPatterns, ¬ Compatible p q v := of_decide_eq_true hc
      exact False.elim (hd (packetPattern w q) (hw q) (compatible_actual w p q hp))

theorem check_split_true {n : ℕ} {catalog : Fin n → Word} {p : Partial}
    {bit : Fin 35} {left right : Tree n}
    (hl : check catalog (Function.update p bit (some false)) left = true)
    (hr : check catalog (Function.update p bit (some true)) right = true) :
    check catalog p (.split bit left right) = true := by
  simpa only [check, Bool.and_eq_true] using And.intro hl hr

theorem check_force_true {n : ℕ} {catalog : Fin n → Word} {p : Partial}
    {q : Fin 35} {k : Fin 4} {b : Bool} {next : Tree n}
    (hf : ForceValid p q k b)
    (hn : check catalog (Function.update p (packetBits q k) (some b)) next = true) :
    check catalog p (.force q k b next) = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hf, hn⟩

def emptyPartial : Partial := fun _ => none

#print axioms check_complete
end Jsp404.N4R2WordTree
