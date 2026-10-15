import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10016 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10017 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h10018 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h10019 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h10020 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 2 3 5 (by decide) (by decide) with h10402 | h10402
  · rcases m.htr 2 4 5 (by decide) (by decide) with h10403 | h10403
    · rcases m.htr 3 4 5 (by decide) (by decide) with h10404 | h10404
      · rcases h2bigk with h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c | h10405c
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h0, hlam, p10405_1]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          rcases p10405_3 (m.d 0 2) (by simp) with h10408 | h10408
          · rcases p10405_3 (m.d 1 2) (by simp) with h10409 | h10409
            · rcases p10405_3 (m.d 2 3) (by simp) with h10410 | h10410
              · linarith only [h10410, hlam, p10405_0]
              · rcases p10405_3 (m.d 2 4) (by simp) with h10412 | h10412
                · linarith only [h10010, h10412, hlam]
                · linarith only [h10020, h10412, hlam]
            · linarith only [h10015, h10409, hlam]
          · linarith only [h10408, hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          rcases p10405_3 (m.d 0 2) (by simp) with h10417 | h10417
          · rcases p10405_3 (m.d 1 2) (by simp) with h10418 | h10418
            · rcases p10405_3 (m.d 2 3) (by simp) with h10419 | h10419
              · linarith only [h10009, h10419, hlam]
              · rcases p10405_3 (m.d 2 4) (by simp) with h10421 | h10421
                · linarith only [h10421, hlam, p10405_0]
                · rcases p10405_3 (m.d 2 5) (by simp) with h10423 | h10423
                  · linarith only [h10011, h10423, hlam]
                  · rcases h3bigk with h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h8410, hlam, p10425_1]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      rcases p10425_3 (m.d 0 3) (by simp) with h10428 | h10428
                      · rcases p10425_3 (m.d 1 3) (by simp) with h10429 | h10429
                        · rcases p10425_3 (m.d 2 3) (by simp) with h10430 | h10430
                          · linarith only [h10009, h10430, hlam]
                          · rcases p10425_3 (m.d 3 4) (by simp) with h10432 | h10432
                            · linarith only [h10012, h10432, hlam]
                            · linarith only [h10020, h10432, hlam]
                        · linarith only [h10015, h10429, hlam]
                      · linarith only [h10009, h10428, hlam]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10015, h10020, h10402, h10404, h8410, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10425_1]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10012, h10020, h10402, hlam, p10425_2]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10015, hc12, hlam, hphi, ht01, p10425_1, u0ehi2]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      rcases p10425_3 (m.d 0 3) (by simp) with h10441 | h10441
                      · linarith only [h10441, h8410, hlam]
                      · linarith only [h10009, h10441, hlam]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10015, h10020, h10402, h10404, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10425_1]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10012, h10020, h10402, h8410, hlam, p10425_2]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10009, hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10015, hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10020, hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10012, h10020, hc03, hc35, hlam, hphi, ht0b, ht5b, p10425_1]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10012, hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10017, hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h0, h10009, h10012, h10402, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10425_1]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      rcases p10425_3 (m.d 0 3) (by simp) with h10455 | h10455
                      · rcases p10425_3 (m.d 1 3) (by simp) with h10456 | h10456
                        · rcases p10425_3 (m.d 2 3) (by simp) with h10457 | h10457
                          · linarith only [h10020, h10457, hlam]
                          · linarith only [h10402, h10457, hlam]
                        · linarith only [h10018, h10456, hlam]
                      · linarith only [h10013, h10455, hlam]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10013, hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10018, hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10402, hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [h10404, hlam, p10425_0]
                    · have p10425_0 := h10425c.1
                      have p10425_1 := h10425c.2.1
                      have p10425_2 := h10425c.2.2.1
                      have p10425_3 := h10425c.2.2.2
                      linarith only [hlam, p10425_0]
            · linarith only [h0, h10418, hlam, p10405_1]
          · linarith only [h10417, hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          rcases p10405_3 (m.d 0 2) (by simp) with h10469 | h10469
          · rcases p10405_3 (m.d 1 2) (by simp) with h10470 | h10470
            · rcases p10405_3 (m.d 2 3) (by simp) with h10471 | h10471
              · linarith only [h10009, h10471, hlam]
              · linarith only [h10402, h10471, hlam]
            · linarith only [h10016, h10470, hlam]
          · linarith only [h10469, hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p10405_1, u0ehi1]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          rcases p10405_3 (m.d 0 2) (by simp) with h10478 | h10478
          · linarith only [h0, h10478, hlam]
          · linarith only [h10009, h10478, hlam]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          rcases p10405_3 (m.d 0 2) (by simp) with h10481 | h10481
          · linarith only [h0, h10481, hlam]
          · linarith only [h10010, h10481, hlam]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          rcases p10405_3 (m.d 0 2) (by simp) with h10484 | h10484
          · linarith only [h0, h10484, hlam]
          · linarith only [h10011, h10484, hlam]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h10009, hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h10015, hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h10020, hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h10009, h10012, h10020, hc02, hc25, hlam, hphi, ht0b, ht5b, p10405_1]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h10010, hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h0, h10009, h10012, h10020, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p10405_1]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h0, h10009, h10012, h10020, h10402, h10404, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10405_1]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          rcases p10405_3 (m.d 0 2) (by simp) with h10496 | h10496
          · rcases p10405_3 (m.d 1 2) (by simp) with h10497 | h10497
            · rcases p10405_3 (m.d 2 3) (by simp) with h10498 | h10498
              · linarith only [h10020, h10498, hlam]
              · linarith only [h10402, h10498, hlam]
            · linarith only [h10016, h10497, hlam]
          · linarith only [h10011, h10496, hlam]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h10011, hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h10016, hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h10402, hlam, p10405_1]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [h10403, hlam, p10405_0]
        · have p10405_0 := h10405c.1
          have p10405_1 := h10405c.2.1
          have p10405_2 := h10405c.2.2.1
          have p10405_3 := h10405c.2.2.2
          linarith only [hlam, p10405_0]
      · linarith only [h10014, h10020, h10402, h10404, hc04, hc35, hlam, hphi, ht0b, ht5b]
    · linarith only [h10008, h10015, h10019, h10020, h10402, h10403, h8410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h10510 | h10510
    · rcases m.htr 3 4 5 (by decide) (by decide) with h10511 | h10511
      · rcases h2bigk with h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c | h10512c
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h0, hlam, p10512_1]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          rcases p10512_3 (m.d 0 2) (by simp) with h10515 | h10515
          · rcases p10512_3 (m.d 1 2) (by simp) with h10516 | h10516
            · rcases p10512_3 (m.d 2 3) (by simp) with h10517 | h10517
              · linarith only [h10517, hlam, p10512_0]
              · rcases p10512_3 (m.d 2 4) (by simp) with h10519 | h10519
                · linarith only [h10010, h10519, hlam]
                · linarith only [h10020, h10519, hlam]
            · linarith only [h10015, h10516, hlam]
          · linarith only [h10515, hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          rcases p10512_3 (m.d 0 2) (by simp) with h10524 | h10524
          · rcases p10512_3 (m.d 1 2) (by simp) with h10525 | h10525
            · rcases p10512_3 (m.d 2 3) (by simp) with h10526 | h10526
              · linarith only [h10009, h10526, hlam]
              · rcases p10512_3 (m.d 2 4) (by simp) with h10528 | h10528
                · linarith only [h10528, hlam, p10512_0]
                · rcases p10512_3 (m.d 2 5) (by simp) with h10530 | h10530
                  · linarith only [h10011, h10530, hlam]
                  · rcases h3bigk with h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c | h10532c
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h8410, hlam, p10532_1]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      rcases p10532_3 (m.d 0 3) (by simp) with h10535 | h10535
                      · rcases p10532_3 (m.d 1 3) (by simp) with h10536 | h10536
                        · rcases p10532_3 (m.d 2 3) (by simp) with h10537 | h10537
                          · linarith only [h10009, h10537, hlam]
                          · rcases p10532_3 (m.d 3 4) (by simp) with h10539 | h10539
                            · linarith only [h10012, h10539, hlam]
                            · linarith only [h10020, h10539, hlam]
                        · linarith only [h10015, h10536, hlam]
                      · linarith only [h10009, h10535, hlam]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      rcases p10532_3 (m.d 0 3) (by simp) with h10544 | h10544
                      · rcases p10532_3 (m.d 1 3) (by simp) with h10545 | h10545
                        · rcases p10532_3 (m.d 2 3) (by simp) with h10546 | h10546
                          · linarith only [h10009, h10546, hlam]
                          · rcases p10532_3 (m.d 3 4) (by simp) with h10548 | h10548
                            · linarith only [h10548, hlam, p10532_0]
                            · rcases p10532_3 (m.d 3 5) (by simp) with h10550 | h10550
                              · linarith only [h10013, h10550, hlam]
                              · rcases h5bigk with h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c | h10552c
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [hlam, p10552_0]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10008, h10015, h8410, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10008, h10015, h8410, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10008, h10015, h10402, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10008, h10015, h8410, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10008, hlam, p10552_0]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [hlam, p10552_0]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10008, h10015, h8410, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10008, h10015, h10402, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10008, h10015, h8410, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10011, hlam, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10016, hlam, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [hlam, p10552_0]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10402, hlam, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h0, h10011, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10013, hlam, p10552_0]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10018, hlam, p10552_0]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h0, h10009, h10013, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [hlam, p10552_0]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h0, h10009, h10511, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10532_1, p10552_1]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10014, hlam, p10552_0]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10019, hlam, p10552_0]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10510, hlam, p10552_0]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [h10511, hlam, p10552_0]
                                · have p10552_0 := h10552c.1
                                  have p10552_1 := h10552c.2.1
                                  have p10552_2 := h10552c.2.2.1
                                  have p10552_3 := h10552c.2.2.2
                                  linarith only [hlam, p10552_0]
                        · linarith only [h10017, h10545, hlam]
                      · linarith only [h10544, hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      rcases p10532_3 (m.d 0 3) (by simp) with h10580 | h10580
                      · rcases p10532_3 (m.d 1 3) (by simp) with h10581 | h10581
                        · rcases p10532_3 (m.d 2 3) (by simp) with h10582 | h10582
                          · linarith only [h10009, h10582, hlam]
                          · rcases p10532_3 (m.d 3 4) (by simp) with h10584 | h10584
                            · linarith only [h10012, h10584, hlam]
                            · linarith only [h10511, h10584, hlam]
                        · linarith only [h10018, h10581, hlam]
                      · linarith only [h10580, hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10015, hc12, hlam, hphi, ht01, p10532_1, u0ehi2]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10008, h10018, h10402, h8410, hlam, p10532_2]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      rcases p10532_3 (m.d 0 3) (by simp) with h10592 | h10592
                      · linarith only [h10592, h8410, hlam]
                      · linarith only [h10012, h10592, hlam]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      rcases p10532_3 (m.d 0 3) (by simp) with h10595 | h10595
                      · linarith only [h10595, h8410, hlam]
                      · linarith only [h10013, h10595, hlam]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10009, hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10015, hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10020, hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10402, hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10012, hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10017, hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      rcases p10532_3 (m.d 0 3) (by simp) with h10605 | h10605
                      · rcases p10532_3 (m.d 1 3) (by simp) with h10606 | h10606
                        · rcases p10532_3 (m.d 2 3) (by simp) with h10607 | h10607
                          · linarith only [h10607, hlam, p10532_0]
                          · rcases p10532_3 (m.d 3 4) (by simp) with h10609 | h10609
                            · rcases p10532_3 (m.d 3 5) (by simp) with h10610 | h10610
                              · linarith only [h10511, h10610, hlam]
                              · linarith only [h10402, h10610, hlam]
                            · linarith only [h10609, hlam, p10532_0]
                        · linarith only [h10015, h10606, hlam]
                      · linarith only [h10009, h10605, hlam]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10012, h10402, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10532_1]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10013, hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10018, hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10008, h10015, h10018, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10532_1]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [h10511, hlam, p10532_0]
                    · have p10532_0 := h10532c.1
                      have p10532_1 := h10532c.2.1
                      have p10532_2 := h10532c.2.2.1
                      have p10532_3 := h10532c.2.2.2
                      linarith only [hlam, p10532_0]
            · linarith only [h0, h10525, hlam, p10512_1]
          · linarith only [h10524, hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          rcases p10512_3 (m.d 0 2) (by simp) with h10625 | h10625
          · rcases p10512_3 (m.d 1 2) (by simp) with h10626 | h10626
            · rcases p10512_3 (m.d 2 3) (by simp) with h10627 | h10627
              · linarith only [h10009, h10627, hlam]
              · rcases p10512_3 (m.d 2 4) (by simp) with h10629 | h10629
                · linarith only [h10010, h10629, hlam]
                · linarith only [h10510, h10629, hlam]
            · linarith only [h10016, h10626, hlam]
          · linarith only [h10625, hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p10512_1, u0ehi1]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h0, h10008, h10018, h10402, hlam, p10512_2]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          rcases p10512_3 (m.d 0 2) (by simp) with h10637 | h10637
          · linarith only [h0, h10637, hlam]
          · linarith only [h10010, h10637, hlam]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          rcases p10512_3 (m.d 0 2) (by simp) with h10640 | h10640
          · linarith only [h0, h10640, hlam]
          · linarith only [h10011, h10640, hlam]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h10009, hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h10015, hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h10020, hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h10402, hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h10010, hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h10015, h8410, hc01, hc24, hlam, hphi, ht12, p10512_1]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          rcases p10512_3 (m.d 0 2) (by simp) with h10650 | h10650
          · rcases p10512_3 (m.d 1 2) (by simp) with h10651 | h10651
            · rcases p10512_3 (m.d 2 3) (by simp) with h10652 | h10652
              · linarith only [h10020, h10652, hlam]
              · rcases p10512_3 (m.d 2 4) (by simp) with h10654 | h10654
                · rcases p10512_3 (m.d 2 5) (by simp) with h10655 | h10655
                  · linarith only [h10510, h10655, hlam]
                  · linarith only [h10402, h10655, hlam]
                · linarith only [h10020, h10654, hlam]
            · linarith only [h10015, h10651, hlam]
          · linarith only [h10009, h10650, hlam]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          rcases p10512_3 (m.d 0 2) (by simp) with h10662 | h10662
          · rcases p10512_3 (m.d 1 2) (by simp) with h10663 | h10663
            · rcases p10512_3 (m.d 2 3) (by simp) with h10664 | h10664
              · linarith only [h10020, h10664, hlam]
              · rcases p10512_3 (m.d 2 4) (by simp) with h10666 | h10666
                · rcases p10512_3 (m.d 2 5) (by simp) with h10667 | h10667
                  · linarith only [h10510, h10667, hlam]
                  · rcases h3bigk with h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c | h10669c
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h8410, hlam, p10669_1]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10012, h10020, h10402, hlam, p10512_1, p10669_2]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h0, h10009, h10020, h10402, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10512_1, p10669_1]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      rcases p10669_3 (m.d 0 3) (by simp) with h10674 | h10674
                      · rcases p10669_3 (m.d 1 3) (by simp) with h10675 | h10675
                        · rcases p10669_3 (m.d 2 3) (by simp) with h10676 | h10676
                          · linarith only [h10009, h10676, hlam]
                          · rcases p10669_3 (m.d 3 4) (by simp) with h10678 | h10678
                            · linarith only [h10012, h10678, hlam]
                            · linarith only [h10511, h10678, hlam]
                        · linarith only [h10018, h10675, hlam]
                      · linarith only [h10674, hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10015, hc12, hlam, hphi, ht01, p10669_1, u0ehi2]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10012, h10020, h10402, h8410, hlam, p10512_1, p10669_2]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10015, h10020, h10402, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10512_1, p10669_1]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      rcases p10669_3 (m.d 0 3) (by simp) with h10687 | h10687
                      · linarith only [h10687, h8410, hlam]
                      · linarith only [h10013, h10687, hlam]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10009, hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10015, hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10020, hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10402, hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10012, hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10017, hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      rcases p10669_3 (m.d 0 3) (by simp) with h10697 | h10697
                      · rcases p10669_3 (m.d 1 3) (by simp) with h10698 | h10698
                        · rcases p10669_3 (m.d 2 3) (by simp) with h10699 | h10699
                          · linarith only [h10699, hlam, p10669_0]
                          · rcases p10669_3 (m.d 3 4) (by simp) with h10701 | h10701
                            · rcases p10669_3 (m.d 3 5) (by simp) with h10702 | h10702
                              · linarith only [h10511, h10702, hlam]
                              · linarith only [h10402, h10702, hlam]
                            · linarith only [h10701, hlam, p10669_0]
                        · linarith only [h10015, h10698, hlam]
                      · linarith only [h10009, h10697, hlam]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10012, h10015, h10402, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10669_1]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10013, hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10018, hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10008, h10015, h10018, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10669_1]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [h10511, hlam, p10669_0]
                    · have p10669_0 := h10669c.1
                      have p10669_1 := h10669c.2.1
                      have p10669_2 := h10669c.2.2.1
                      have p10669_3 := h10669c.2.2.2
                      linarith only [hlam, p10669_0]
                · linarith only [h10510, h10666, hlam]
            · linarith only [h10016, h10663, hlam]
          · linarith only [h10011, h10662, hlam]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h10011, hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h10016, hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h10008, h10015, h10016, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10512_1]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [h10510, hlam, p10512_0]
        · have p10512_0 := h10512c.1
          have p10512_1 := h10512c.2.1
          have p10512_2 := h10512c.2.2.1
          have p10512_3 := h10512c.2.2.2
          linarith only [hlam, p10512_0]
      · linarith only [h0, h10008, h10019, h10020, h10511, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h10724 | h10724
      · rcases h2bigk with h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c | h10725c
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h0, hlam, p10725_1]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10009, h10012, h10020, h10510, h10724, hlam, p10725_2]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10009, h10012, h10510, h10724, hlam, p10725_2]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          rcases p10725_3 (m.d 0 2) (by simp) with h10730 | h10730
          · rcases p10725_3 (m.d 1 2) (by simp) with h10731 | h10731
            · rcases p10725_3 (m.d 2 3) (by simp) with h10732 | h10732
              · linarith only [h10009, h10732, hlam]
              · rcases p10725_3 (m.d 2 4) (by simp) with h10734 | h10734
                · linarith only [h10010, h10734, hlam]
                · rcases p10725_3 (m.d 2 5) (by simp) with h10736 | h10736
                  · linarith only [h10736, hlam, p10725_0]
                  · rcases h3bigk with h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c | h10738c
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h8410, hlam, p10738_1]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10012, h10020, h10510, h10724, hlam, p10738_2]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10020, h10510, h10724, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10738_1]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      rcases p10738_3 (m.d 0 3) (by simp) with h10743 | h10743
                      · rcases p10738_3 (m.d 1 3) (by simp) with h10744 | h10744
                        · rcases p10738_3 (m.d 2 3) (by simp) with h10745 | h10745
                          · linarith only [h10009, h10745, hlam]
                          · rcases p10738_3 (m.d 3 4) (by simp) with h10747 | h10747
                            · linarith only [h10012, h10747, hlam]
                            · linarith only [h10724, h10747, hlam]
                        · linarith only [h10018, h10744, hlam]
                      · linarith only [h10743, hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10015, hc12, hlam, hphi, ht01, p10738_1, u0ehi2]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10008, h10018, h10020, h10510, h10724, h8410, hlam, p10738_2]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10015, h10020, h10510, h10724, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10738_1]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      rcases p10738_3 (m.d 0 3) (by simp) with h10756 | h10756
                      · linarith only [h10756, h8410, hlam]
                      · linarith only [h10013, h10756, hlam]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10009, hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10015, hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10020, hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10402, hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10012, hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10017, hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      rcases p10738_3 (m.d 0 3) (by simp) with h10766 | h10766
                      · rcases p10738_3 (m.d 1 3) (by simp) with h10767 | h10767
                        · rcases p10738_3 (m.d 2 3) (by simp) with h10768 | h10768
                          · linarith only [h10768, hlam, p10738_0]
                          · rcases p10738_3 (m.d 3 4) (by simp) with h10770 | h10770
                            · rcases p10738_3 (m.d 3 5) (by simp) with h10771 | h10771
                              · linarith only [h10724, h10771, hlam]
                              · linarith only [h10402, h10771, hlam]
                            · linarith only [h10770, hlam, p10738_0]
                        · linarith only [h10015, h10767, hlam]
                      · linarith only [h10009, h10766, hlam]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10012, h10020, h10510, h10724, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10738_1]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10013, hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10018, hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10008, h10015, h10018, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10738_1]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [h10724, hlam, p10738_0]
                    · have p10738_0 := h10738c.1
                      have p10738_1 := h10738c.2.1
                      have p10738_2 := h10738c.2.2.1
                      have p10738_3 := h10738c.2.2.2
                      linarith only [hlam, p10738_0]
            · linarith only [h10016, h10731, hlam]
          · linarith only [h10730, hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p10725_1, u0ehi1]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10008, h10015, h10019, h10020, h10510, h8410, hlam, p10725_2]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10008, h10015, h10018, h10510, h10724, h8410, hlam, p10725_2]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          rcases p10725_3 (m.d 0 2) (by simp) with h10790 | h10790
          · linarith only [h0, h10790, hlam]
          · linarith only [h10011, h10790, hlam]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10009, hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10015, hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10020, hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10402, hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10010, hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10008, h10015, h10018, h10510, h10724, h8410, hlam, p10725_1]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10008, h10015, h10018, h10510, h10724, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10725_1]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10510, hlam, p10725_1]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10011, hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10016, hlam, p10725_0]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10008, h10015, h10018, h10510, h10724, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10725_1]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [h10008, h10015, h10018, h10510, h10724, h8410, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10725_1]
        · have p10725_0 := h10725c.1
          have p10725_1 := h10725c.2.1
          have p10725_2 := h10725c.2.2.1
          have p10725_3 := h10725c.2.2.2
          linarith only [hlam, p10725_0]
      · linarith only [h10008, h10015, h10019, h10020, h10724, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10016 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10017 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h10018 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h10019 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 2 3 4 (by decide) (by decide) with h10020 | h10020
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015 h10016 h10017 h10018 h10019 h10020
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015 h10016 h10017 h10018 h10019 h10020

end R2N4
