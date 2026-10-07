import Jsp000404.SixOuterReplaySoundness
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Bits

/-! SOURCE_ONLY until genuine strict and normal kernel checks.
The catalog is a necessary consequence of actual triangle inequalities alone.
The proof splits the new ten-bit WordSound, closes cyclic prefixes by linear
arithmetic, and proves literal catalog membership at the remaining leaves.
No HIGH, row-defect, caller acyclicity, row sorting, solver, or rank-region
premise is used. The old between terminal is not invoked or imported.
-/

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 4096

namespace Jsp404.SixOuterWordCatalogComplete
open SatScalarModel SixOuterReplay SixOuterReplaySoundness

/-- In the new triples order, bit 0 is 012 and true selects the reverse arm.
The numerical encoding is little endian. -/
def masks : List ℕ := [0, 1, 3, 7, 11, 15, 31, 63, 64, 72, 74, 75, 79, 95, 127, 192, 200, 202, 216, 218, 222, 223, 254, 255, 448, 456, 472, 504, 508, 510, 511, 512, 513, 515, 519, 551, 567, 575, 768, 769, 800, 801, 805, 807, 821, 823, 831, 896, 928, 944, 948, 949, 951, 959, 960, 992, 1008, 1012, 1016, 1020, 1022, 1023]

abbrev catalogMasks := masks

theorem masks_length : masks.length = 62 := by decide

def encodeWord (w : Word) : ℕ :=
  (if w (0 : Fin 10) then 1 else 0) +
    (if w (1 : Fin 10) then 2 else 0) +
    (if w (2 : Fin 10) then 4 else 0) +
    (if w (3 : Fin 10) then 8 else 0) +
    (if w (4 : Fin 10) then 16 else 0) +
    (if w (5 : Fin 10) then 32 else 0) +
    (if w (6 : Fin 10) then 64 else 0) +
    (if w (7 : Fin 10) then 128 else 0) +
    (if w (8 : Fin 10) then 256 else 0) +
    (if w (9 : Fin 10) then 512 else 0)

theorem encodeWord_bound (w : Word) : encodeWord w < 1024 := by
  have hb0 : (if w (0 : Fin 10) then 1 else 0) ≤ 1 := by
    cases h : w (0 : Fin 10) <;> simp [h]
  have hb1 : (if w (1 : Fin 10) then 2 else 0) ≤ 2 := by
    cases h : w (1 : Fin 10) <;> simp [h]
  have hb2 : (if w (2 : Fin 10) then 4 else 0) ≤ 4 := by
    cases h : w (2 : Fin 10) <;> simp [h]
  have hb3 : (if w (3 : Fin 10) then 8 else 0) ≤ 8 := by
    cases h : w (3 : Fin 10) <;> simp [h]
  have hb4 : (if w (4 : Fin 10) then 16 else 0) ≤ 16 := by
    cases h : w (4 : Fin 10) <;> simp [h]
  have hb5 : (if w (5 : Fin 10) then 32 else 0) ≤ 32 := by
    cases h : w (5 : Fin 10) <;> simp [h]
  have hb6 : (if w (6 : Fin 10) then 64 else 0) ≤ 64 := by
    cases h : w (6 : Fin 10) <;> simp [h]
  have hb7 : (if w (7 : Fin 10) then 128 else 0) ≤ 128 := by
    cases h : w (7 : Fin 10) <;> simp [h]
  have hb8 : (if w (8 : Fin 10) then 256 else 0) ≤ 256 := by
    cases h : w (8 : Fin 10) <;> simp [h]
  have hb9 : (if w (9 : Fin 10) then 512 else 0) ≤ 512 := by
    cases h : w (9 : Fin 10) <;> simp [h]
  unfold encodeWord
  omega

private theorem catalog_values_lt : ∀ c : Fin 62, masks[c.val]! < 1024 := by decide

def catalog (c : Fin 62) : Fin 1024 := ⟨masks[c.val]!, catalog_values_lt c⟩

def wordOfMask (code : Fin 1024) : Word := fun t => code.val.testBit t.val

/-- All ten chosen actual triangle arms imply membership in the 62-word
catalog, independently of the floor profiles and delta range. -/
theorem model_catalog_membership (M : GenericModel 5 4) (w : Word)
    (hword : WordSound M w) : encodeWord w ∈ masks := by
  cases hbit0 : w (0 : Fin 10)
  ·
    have htri012 := hword (0 : Fin 10)
    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit0] at htri012
    have htr012a := htri012.1
    have htr012b := htri012.2.1
    have htr012c := htri012.2.2
    cases hbit1 : w (1 : Fin 10)
    ·
      have htri013 := hword (1 : Fin 10)
      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit1] at htri013
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      cases hbit2 : w (2 : Fin 10)
      ·
        have htri014 := hword (2 : Fin 10)
        norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit2] at htri014
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        cases hbit3 : w (3 : Fin 10)
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123c, htr134a, htr234a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134b, htr123b, htr124c]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134b, htr123a, htr124c, htr234a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr124b, htr234a, htr134c, htr123a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr124b, htr123c, htr134c]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123b, htr234a, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr134a, htr034a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr123c, htr134c, htr124b]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr023b, htr034b, htr024c]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr023a, htr024a, htr124a, htr123a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013c, htr023b, htr134a, htr234a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134c, htr123c, htr124b]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023a, htr024a, htr134c, htr124b, htr234a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023a, htr024b, htr234a, htr034c]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr024b, htr034c, htr023c]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr124a, htr012c]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013c, htr023b, htr234a, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013c, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
      ·
        have htri014 := hword (2 : Fin 10)
        norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit2] at htri014
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        cases hbit3 : w (3 : Fin 10)
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr012b, htr014c, htr024b]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr023b, htr012b, htr014c, htr034b]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134b, htr014a, htr012a, htr234a, htr123a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr023a, htr123a, htr124a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr134a, htr034a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr014a, htr023a, htr012b, htr234a, htr134b]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr013b, htr023c, htr024b, htr014c]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr013b, htr014c, htr034b]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr123a, htr012c, htr023a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012c, htr124a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013c, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
    ·
      have htri013 := hword (1 : Fin 10)
      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit1] at htri013
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      cases hbit2 : w (2 : Fin 10)
      ·
        have htri014 := hword (2 : Fin 10)
        norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit2] at htri014
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        cases hbit3 : w (3 : Fin 10)
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr023b, htr013c, htr012b]
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr234a, htr013a, htr012a, htr123b, htr134c, htr124b]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr024a, htr013a, htr012b, htr234a, htr134c, htr123b, htr124b]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr034c, htr013c, htr012b, htr024b]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012c, htr123a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr012c, htr024a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr014a, htr013a, htr123b, htr234a, htr134c]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr014b, htr034c, htr013c]
      ·
        have htri014 := hword (2 : Fin 10)
        norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit2] at htri014
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        cases hbit3 : w (3 : Fin 10)
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr013c, htr012b, htr023b]
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr014c, htr012b, htr024b]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012c, htr023a, htr123a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr024a, htr012c]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr034a, htr013b, htr234a, htr123b]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr123a, htr012c, htr023a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr024a, htr012c]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134a, htr234a, htr123b]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
  ·
    have htri012 := hword (0 : Fin 10)
    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit0] at htri012
    have htr012a := htri012.1
    have htr012b := htri012.2.1
    have htr012c := htri012.2.2
    cases hbit1 : w (1 : Fin 10)
    ·
      have htri013 := hword (1 : Fin 10)
      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit1] at htri013
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      cases hbit2 : w (2 : Fin 10)
      ·
        have htri014 := hword (2 : Fin 10)
        norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit2] at htri014
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        cases hbit3 : w (3 : Fin 10)
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr234a, htr123c, htr134a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012b, htr124a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr123a, htr023a]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr134a, htr034a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013c, htr123c, htr234a, htr034a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr024a, htr012b]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr023a, htr123a]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr012c, htr014b, htr024c]
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr012c, htr013b, htr023c]
      ·
        have htri014 := hword (2 : Fin 10)
        norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit2] at htri014
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        cases hbit3 : w (3 : Fin 10)
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr013b, htr034b, htr014c]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr014a, htr013a, htr134b, htr123c, htr234a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012b, htr124a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012b, htr123a]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr012c, htr013b, htr024c, htr034b]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr012c, htr234a, htr013a, htr024a, htr124c, htr123c, htr134b]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013c, htr034a, htr134a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013a, htr134b, htr012a, htr123c, htr234a, htr124c]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr123a, htr012b]
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          linarith only [htr012c, htr023c, htr013b]
    ·
      have htri013 := hword (1 : Fin 10)
      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit1] at htri013
      have htr013a := htri013.1
      have htr013b := htri013.2.1
      have htr013c := htri013.2.2
      cases hbit2 : w (2 : Fin 10)
      ·
        have htri014 := hword (2 : Fin 10)
        norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit2] at htri014
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        cases hbit3 : w (3 : Fin 10)
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr024a, htr012b, htr124a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr023a, htr012b, htr123a]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr014b, htr034c, htr013c]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr014b, htr024c, htr023b, htr013c]
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr012c, htr134c, htr014a, htr023a, htr234a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr134a, htr034a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr123a, htr023a, htr024a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134c, htr123a, htr012a, htr014a, htr234a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr134a, htr034a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr012b, htr124a, htr024a]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr012c, htr023c, htr034c, htr014b]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            linarith only [htr012c, htr014b, htr024c]
      ·
        have htri014 := hword (2 : Fin 10)
        norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit2] at htri014
        have htr014a := htri014.1
        have htr014b := htri014.2.1
        have htr014c := htri014.2.2
        cases hbit3 : w (3 : Fin 10)
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr134a, htr034a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr012b, htr124a, htr024a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr023a, htr123a]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023c, htr034a, htr234a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013b, htr023c, htr134a, htr234a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr012b, htr024a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr123a, htr012b, htr023a]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr034b, htr024c, htr023b]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr034b, htr234a, htr023a, htr024c]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr024a, htr234a, htr023a, htr134b, htr124c]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134b, htr124c, htr123b]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr013b, htr234a, htr023c, htr134a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                linarith only [htr012b, htr123a, htr023a]
        ·
          have htri023 := hword (3 : Fin 10)
          norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit3] at htri023
          have htr023a := htri023.1
          have htr023b := htri023.2.1
          have htr023c := htri023.2.2
          cases hbit4 : w (4 : Fin 10)
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr123a, htr023a, htr024a, htr124a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr034a, htr013b, htr134a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  linarith only [htr124a, htr012b, htr024a]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              linarith only [htr023c, htr024b, htr034c]
          ·
            have htri024 := hword (4 : Fin 10)
            norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit4] at htri024
            have htr024a := htri024.1
            have htr024b := htri024.2.1
            have htr024c := htri024.2.2
            cases hbit5 : w (5 : Fin 10)
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr234a, htr023b, htr034a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr124c, htr123b, htr134b]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr234a, htr034a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134a, htr013b, htr034a]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr023b, htr034a, htr234a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr013b, htr034a, htr134a]
            ·
              have htri034 := hword (5 : Fin 10)
              norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit5] at htri034
              have htr034a := htri034.1
              have htr034b := htri034.2.1
              have htr034c := htri034.2.2
              cases hbit6 : w (6 : Fin 10)
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123c, htr234a, htr134a]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr123b, htr134b, htr124c]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr123a, htr234a, htr134b, htr124c]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
              ·
                have htri123 := hword (6 : Fin 10)
                norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit6] at htri123
                have htr123a := htri123.1
                have htr123b := htri123.2.1
                have htr123c := htri123.2.2
                cases hbit7 : w (7 : Fin 10)
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134c, htr124b, htr123a, htr234a]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    linarith only [htr134c, htr123c, htr124b]
                ·
                  have htri124 := hword (7 : Fin 10)
                  norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit7] at htri124
                  have htr124a := htri124.1
                  have htr124b := htri124.2.1
                  have htr124c := htri124.2.2
                  cases hbit8 : w (8 : Fin 10)
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      linarith only [htr134a, htr234a, htr123b]
                  ·
                    have htri134 := hword (8 : Fin 10)
                    norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit8] at htri134
                    have htr134a := htri134.1
                    have htr134b := htri134.2.1
                    have htr134c := htri134.2.2
                    cases hbit9 : w (9 : Fin 10)
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]
                    ·
                      have htri234 := hword (9 : Fin 10)
                      norm_num [WordSound, triples, triangleLow, triangleHigh, value, hbit9] at htri234
                      have htr234a := htri234.1
                      have htr234b := htri234.2.1
                      have htr234c := htri234.2.2
                      norm_num [encodeWord, masks, hbit0, hbit1, hbit2, hbit3, hbit4, hbit5, hbit6, hbit7, hbit8, hbit9]

/-- Finite encoding inversion; this is a closed 1024-word check, not a
geometric hypothesis supplied by a caller. -/
theorem wordOfMask_encode (w : Word) :
    wordOfMask ⟨encodeWord w, encodeWord_bound w⟩ = w := by
  let packed : ℕ := Nat.bit (w (0 : Fin 10)) (Nat.bit (w (1 : Fin 10)) (Nat.bit (w (2 : Fin 10)) (Nat.bit (w (3 : Fin 10)) (Nat.bit (w (4 : Fin 10)) (Nat.bit (w (5 : Fin 10)) (Nat.bit (w (6 : Fin 10)) (Nat.bit (w (7 : Fin 10)) (Nat.bit (w (8 : Fin 10)) (Nat.bit (w (9 : Fin 10)) (0))))))))))
  have hb0 : (if w (0 : Fin 10) then 1 else 0) =
      1 * (w (0 : Fin 10)).toNat := by
    cases w (0 : Fin 10) <;> rfl
  have hb1 : (if w (1 : Fin 10) then 2 else 0) =
      2 * (w (1 : Fin 10)).toNat := by
    cases w (1 : Fin 10) <;> rfl
  have hb2 : (if w (2 : Fin 10) then 4 else 0) =
      4 * (w (2 : Fin 10)).toNat := by
    cases w (2 : Fin 10) <;> rfl
  have hb3 : (if w (3 : Fin 10) then 8 else 0) =
      8 * (w (3 : Fin 10)).toNat := by
    cases w (3 : Fin 10) <;> rfl
  have hb4 : (if w (4 : Fin 10) then 16 else 0) =
      16 * (w (4 : Fin 10)).toNat := by
    cases w (4 : Fin 10) <;> rfl
  have hb5 : (if w (5 : Fin 10) then 32 else 0) =
      32 * (w (5 : Fin 10)).toNat := by
    cases w (5 : Fin 10) <;> rfl
  have hb6 : (if w (6 : Fin 10) then 64 else 0) =
      64 * (w (6 : Fin 10)).toNat := by
    cases w (6 : Fin 10) <;> rfl
  have hb7 : (if w (7 : Fin 10) then 128 else 0) =
      128 * (w (7 : Fin 10)).toNat := by
    cases w (7 : Fin 10) <;> rfl
  have hb8 : (if w (8 : Fin 10) then 256 else 0) =
      256 * (w (8 : Fin 10)).toNat := by
    cases w (8 : Fin 10) <;> rfl
  have hb9 : (if w (9 : Fin 10) then 512 else 0) =
      512 * (w (9 : Fin 10)).toNat := by
    cases w (9 : Fin 10) <;> rfl
  have hpacked : encodeWord w = packed := by
    dsimp [packed]
    simp only [encodeWord, Nat.bit_val, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9]
    omega
  funext t
  change (encodeWord w).testBit t.val = w t
  rw [hpacked]
  fin_cases t <;> simp [packed, Nat.testBit_bit_zero, Nat.testBit_bit_succ]

private theorem catalog_codes_complete : ∀ code : Fin 1024,
    code.val ∈ masks → ∃ c : Fin 62, catalog c = code := by decide

theorem model_catalog_index (M : GenericModel 5 4) (w : Word)
    (hword : WordSound M w) : ∃ c : Fin 62, w = wordOfMask (catalog c) := by
  let code : Fin 1024 := ⟨encodeWord w, encodeWord_bound w⟩
  obtain ⟨c, hc⟩ := catalog_codes_complete code (model_catalog_membership M w hword)
  refine ⟨c, ?_⟩
  rw [hc]
  exact (wordOfMask_encode w).symm

/-- The actual model provides its word internally. No mask, acyclicity,
HIGH/profile restriction, callback, or certificate is a premise. -/
theorem exists_catalog_model_word (M : GenericModel 5 4) :
    ∃ c : Fin 62, WordSound M (wordOfMask (catalog c)) := by
  obtain ⟨w, hword⟩ := SixOuterReplaySoundness.exists_sound_word M
  obtain ⟨c, hc⟩ := model_catalog_index M w hword
  refine ⟨c, ?_⟩
  rw [← hc]
  exact hword

#print axioms masks_length
#print axioms encodeWord_bound
#print axioms model_catalog_membership
#print axioms wordOfMask_encode
#print axioms model_catalog_index
#print axioms exists_catalog_model_word
end Jsp404.SixOuterWordCatalogComplete
