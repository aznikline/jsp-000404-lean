import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9896 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h9897 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h9898 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h10456 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h10458 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 3 4 5 (by decide) (by decide) with h10459 | h10459
  · rcases h0bigk with h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c | h10460c
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [hlam, p10460_0]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h0, hlam, p10460_1]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h7600, hlam, p10460_0]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h8836, hlam, p10460_1]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h9666, hlam, p10460_1]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      rcases p10460_3 (m.d 0 1) (by simp) with h10466 | h10466
      · linarith only [h0, h10466, hlam]
      · rcases p10460_3 (m.d 0 2) (by simp) with h10468 | h10468
        · rcases p10460_3 (m.d 0 3) (by simp) with h10469 | h10469
          · linarith only [h10469, h9886, hlam]
          · linarith only [h10469, h7600, hlam]
        · linarith only [h0, h10468, hlam]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [hlam, p10460_0]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h0, h10456, h10459, h9889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10460_1]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h0, h9891, hc12, hlam, hphi, ht01, ht0b, ht5b, p10460_1, u5ehi4]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      rcases p10460_3 (m.d 0 1) (by simp) with h10476 | h10476
      · linarith only [h0, h10476, hlam]
      · rcases p10460_3 (m.d 0 2) (by simp) with h10478 | h10478
        · rcases p10460_3 (m.d 0 3) (by simp) with h10479 | h10479
          · linarith only [h10479, h9886, hlam]
          · linarith only [h10479, h9890, hlam]
        · linarith only [h10478, h9888, hlam]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      rcases p10460_3 (m.d 0 1) (by simp) with h10483 | h10483
      · linarith only [h10483, h7600, hlam]
      · rcases p10460_3 (m.d 0 2) (by simp) with h10485 | h10485
        · rcases p10460_3 (m.d 0 3) (by simp) with h10486 | h10486
          · rcases p10460_3 (m.d 0 4) (by simp) with h10487 | h10487
            · linarith only [h10487, h9889, hlam]
            · linarith only [h10487, h8836, hlam]
          · linarith only [h10486, h7600, hlam]
        · linarith only [h0, h10485, hlam]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h9886, hlam, p10460_1]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [hlam, p10460_0]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h10458, h9889, h9898, hc03, hlam, hphi, ht0b, ht5b, p10460_1, u5ehi4]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      rcases p10460_3 (m.d 0 1) (by simp) with h10495 | h10495
      · linarith only [h10495, h7600, hlam]
      · rcases p10460_3 (m.d 0 2) (by simp) with h10497 | h10497
        · rcases p10460_3 (m.d 0 3) (by simp) with h10498 | h10498
          · rcases p10460_3 (m.d 0 4) (by simp) with h10499 | h10499
            · linarith only [h10499, h9889, hlam]
            · linarith only [h10499, h9891, hlam]
          · linarith only [h10498, h9890, hlam]
        · linarith only [h10497, h9888, hlam]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      rcases p10460_3 (m.d 0 1) (by simp) with h10504 | h10504
      · linarith only [h10504, h8836, hlam]
      · rcases p10460_3 (m.d 0 2) (by simp) with h10506 | h10506
        · rcases p10460_3 (m.d 0 3) (by simp) with h10507 | h10507
          · rcases p10460_3 (m.d 0 4) (by simp) with h10508 | h10508
            · rcases p10460_3 (m.d 0 5) (by simp) with h10509 | h10509
              · linarith only [h10509, h9891, hlam]
              · linarith only [h10509, h9666, hlam]
            · linarith only [h10508, h8836, hlam]
          · linarith only [h10507, h7600, hlam]
        · linarith only [h0, h10506, hlam]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h9887, hlam, p10460_0]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h9889, hlam, p10460_0]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [hlam, p10460_0]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      rcases p10460_3 (m.d 0 1) (by simp) with h10518 | h10518
      · linarith only [h10518, h8836, hlam]
      · rcases p10460_3 (m.d 0 2) (by simp) with h10520 | h10520
        · rcases p10460_3 (m.d 0 3) (by simp) with h10521 | h10521
          · rcases p10460_3 (m.d 0 4) (by simp) with h10522 | h10522
            · rcases p10460_3 (m.d 0 5) (by simp) with h10523 | h10523
              · linarith only [h10523, h9891, hlam]
              · rcases h2bigk with h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c | h10525c
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h0, hlam, p10525_1]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h10456, h9886, h9889, h9890, hlam, p10460_1, p10525_2]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h10458, hc02, hlam, hphi, ht0b, ht5b, p10525_1, u5ehi4]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  rcases p10525_3 (m.d 0 2) (by simp) with h10530 | h10530
                  · rcases p10525_3 (m.d 1 2) (by simp) with h10531 | h10531
                    · rcases p10525_3 (m.d 2 3) (by simp) with h10532 | h10532
                      · linarith only [h10532, h9886, hlam]
                      · rcases p10525_3 (m.d 2 4) (by simp) with h10534 | h10534
                        · linarith only [h10534, h9887, hlam]
                        · linarith only [h10458, h10534, hlam]
                    · linarith only [h10531, h9894, hlam]
                  · linarith only [h10530, hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h10456, h9886, h9889, h9890, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10460_1, p10525_1]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h0, h10456, h9886, h9889, h9890, hlam, p10460_1, p10525_2]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h10458, hc12, hlam, hphi, ht01, ht0b, ht5b, p10525_1, u5ehi4]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  rcases p10525_3 (m.d 0 2) (by simp) with h10543 | h10543
                  · linarith only [h0, h10543, hlam]
                  · linarith only [h10543, h9888, hlam]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h9886, hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h9892, hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h9898, hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h10456, hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h9887, hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h9893, hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  rcases p10525_3 (m.d 0 2) (by simp) with h10553 | h10553
                  · rcases p10525_3 (m.d 1 2) (by simp) with h10554 | h10554
                    · rcases p10525_3 (m.d 2 3) (by simp) with h10555 | h10555
                      · linarith only [h10555, h9898, hlam]
                      · rcases p10525_3 (m.d 2 4) (by simp) with h10557 | h10557
                        · rcases p10525_3 (m.d 2 5) (by simp) with h10558 | h10558
                          · linarith only [h10458, h10558, hlam]
                          · linarith only [h10456, h10558, hlam]
                        · linarith only [h10557, h9898, hlam]
                    · linarith only [h10554, h9892, hlam]
                  · linarith only [h10553, h9886, hlam]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h10458, h9887, hc02, hlam, hphi, ht0b, ht5b, p10525_1, u5ehi4]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h9888, hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h9894, hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h9888, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10460_1, p10525_1]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [h10458, hlam, p10525_0]
                · have p10525_0 := h10525c.1
                  have p10525_1 := h10525c.2.1
                  have p10525_2 := h10525c.2.2.1
                  have p10525_3 := h10525c.2.2.2
                  linarith only [hlam, p10525_0]
            · linarith only [h10522, h9891, hlam]
          · linarith only [h10521, h9890, hlam]
        · linarith only [h10520, h9888, hlam]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      rcases p10460_3 (m.d 0 1) (by simp) with h10574 | h10574
      · linarith only [h10574, h9666, hlam]
      · rcases p10460_3 (m.d 0 2) (by simp) with h10576 | h10576
        · rcases p10460_3 (m.d 0 3) (by simp) with h10577 | h10577
          · rcases p10460_3 (m.d 0 4) (by simp) with h10578 | h10578
            · rcases p10460_3 (m.d 0 5) (by simp) with h10579 | h10579
              · rcases h2bigk with h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c | h10580c
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h0, hlam, p10580_1]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  rcases p10580_3 (m.d 0 2) (by simp) with h10583 | h10583
                  · rcases p10580_3 (m.d 1 2) (by simp) with h10584 | h10584
                    · rcases p10580_3 (m.d 2 3) (by simp) with h10585 | h10585
                      · linarith only [h10585, hlam, p10580_0]
                      · rcases p10580_3 (m.d 2 4) (by simp) with h10587 | h10587
                        · linarith only [h10587, h9887, hlam]
                        · linarith only [h10587, h9898, hlam]
                    · linarith only [h10584, h9892, hlam]
                  · linarith only [h10583, hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h10458, hc02, hlam, hphi, ht0b, ht5b, p10580_1, u5ehi4]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  rcases p10580_3 (m.d 0 2) (by simp) with h10593 | h10593
                  · rcases p10580_3 (m.d 1 2) (by simp) with h10594 | h10594
                    · rcases p10580_3 (m.d 2 3) (by simp) with h10595 | h10595
                      · linarith only [h10595, h9886, hlam]
                      · rcases p10580_3 (m.d 2 4) (by simp) with h10597 | h10597
                        · linarith only [h10597, h9887, hlam]
                        · linarith only [h10458, h10597, hlam]
                    · linarith only [h10594, h9894, hlam]
                  · linarith only [h10593, hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h10458, h9886, h9889, h9898, hc12, hlam, hphi, ht01, ht0b, ht5b, p10580_1, u5ehi4]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  rcases p10580_3 (m.d 0 2) (by simp) with h10604 | h10604
                  · linarith only [h0, h10604, hlam]
                  · linarith only [h10604, h9886, hlam]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h10458, hc12, hlam, hphi, ht01, ht0b, ht5b, p10580_1, u5ehi4]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  rcases p10580_3 (m.d 0 2) (by simp) with h10608 | h10608
                  · linarith only [h0, h10608, hlam]
                  · linarith only [h10608, h9888, hlam]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h9886, hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h9892, hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h9898, hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h10456, hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h9887, hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h9893, hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  rcases p10580_3 (m.d 0 2) (by simp) with h10618 | h10618
                  · rcases p10580_3 (m.d 1 2) (by simp) with h10619 | h10619
                    · rcases p10580_3 (m.d 2 3) (by simp) with h10620 | h10620
                      · linarith only [h10620, h9898, hlam]
                      · rcases p10580_3 (m.d 2 4) (by simp) with h10622 | h10622
                        · rcases p10580_3 (m.d 2 5) (by simp) with h10623 | h10623
                          · linarith only [h10458, h10623, hlam]
                          · linarith only [h10456, h10623, hlam]
                        · linarith only [h10622, h9898, hlam]
                    · linarith only [h10619, h9892, hlam]
                  · linarith only [h10618, h9886, hlam]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h10458, h9886, h9889, h9898, hc02, hlam, hphi, ht0b, ht5b, p10580_1, u5ehi4]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h9888, hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h9894, hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  rcases p10580_3 (m.d 0 2) (by simp) with h10633 | h10633
                  · rcases p10580_3 (m.d 1 2) (by simp) with h10634 | h10634
                    · rcases p10580_3 (m.d 2 3) (by simp) with h10635 | h10635
                      · linarith only [h10456, h10635, hlam]
                      · rcases p10580_3 (m.d 2 4) (by simp) with h10637 | h10637
                        · rcases p10580_3 (m.d 2 5) (by simp) with h10638 | h10638
                          · rcases h3bigk with h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c | h10639c
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h7600, hlam, p10639_1]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h10456, h10459, h9889, hlam, p10580_1, p10639_2]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h0, h10456, h10459, h9886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10580_1, p10639_1]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h0, h10456, h9886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10580_1, p10639_1]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h10456, h10459, h9889, h9892, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10580_1, p10639_1]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h10456, h10459, h7600, h9889, hlam, p10580_1, p10639_2]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h10456, h10459, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10580_1, p10639_1]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h10456, h9892, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10580_1, p10639_1]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h9886, hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h9892, hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h9898, hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h10456, hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h9889, hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h9895, hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              rcases p10639_3 (m.d 0 3) (by simp) with h10657 | h10657
                              · rcases p10639_3 (m.d 1 3) (by simp) with h10658 | h10658
                                · rcases p10639_3 (m.d 2 3) (by simp) with h10659 | h10659
                                  · linarith only [h10659, hlam, p10639_0]
                                  · rcases p10639_3 (m.d 3 4) (by simp) with h10661 | h10661
                                    · rcases p10639_3 (m.d 3 5) (by simp) with h10662 | h10662
                                      · linarith only [h10459, h10662, hlam]
                                      · linarith only [h10456, h10662, hlam]
                                    · linarith only [h10661, hlam, p10639_0]
                                · linarith only [h10658, h9892, hlam]
                              · linarith only [h10657, h9886, hlam]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h10456, h9889, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10580_1, p10639_1]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h9890, hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h9896, hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              rcases p10639_3 (m.d 0 3) (by simp) with h10672 | h10672
                              · rcases p10639_3 (m.d 1 3) (by simp) with h10673 | h10673
                                · rcases p10639_3 (m.d 2 3) (by simp) with h10674 | h10674
                                  · linarith only [h10674, hlam, p10639_0]
                                  · rcases p10639_3 (m.d 3 4) (by simp) with h10676 | h10676
                                    · rcases p10639_3 (m.d 3 5) (by simp) with h10677 | h10677
                                      · rcases h5bigk with h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c | h10678c
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [hlam, p10678_0]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h9666, hlam, p10678_1]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10580_1, p10678_1]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h10456, h7600, h9890, h9892, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10580_1, p10678_1]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          rcases p10678_3 (m.d 0 5) (by simp) with h10683 | h10683
                                          · rcases p10678_3 (m.d 1 5) (by simp) with h10684 | h10684
                                            · rcases p10678_3 (m.d 2 5) (by simp) with h10685 | h10685
                                              · linarith only [h10685, h9888, hlam]
                                              · linarith only [h10458, h10685, hlam]
                                            · linarith only [h10684, h9897, hlam]
                                          · linarith only [h10683, h9891, hlam]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h9892, h9895, h9897, hc01, hc12, hlam, hphi, p10460_1, p10678_1]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [hlam, p10678_0]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h9892, h9895, h9897, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10580_1, p10678_1]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h10456, h9892, h9895, h9897, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10580_1, p10678_1]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          rcases p10678_3 (m.d 0 5) (by simp) with h10694 | h10694
                                          · linarith only [h10694, h9666, hlam]
                                          · linarith only [h10694, h9891, hlam]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h9888, hlam, p10678_1]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h9894, hlam, p10678_1]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [hlam, p10678_0]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h10456, hlam, p10678_1]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h0, h9888, hc12, hlam, hphi, ht01, ht0b, ht5b, p10678_1, u5ehi4]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h9890, hlam, p10678_0]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h9896, hlam, p10678_0]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h7600, h9890, h9892, hc12, hlam, hphi, ht01, ht0b, ht5b, p10678_1, u5ehi2]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [hlam, p10678_0]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h10459, h7600, h9889, h9892, hc12, hlam, hphi, ht01, ht0b, ht5b, p10678_1, u5ehi4]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h9891, hlam, p10678_0]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h9897, hlam, p10678_0]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h10458, hlam, p10678_0]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [h10459, hlam, p10678_0]
                                        · have p10678_0 := h10678c.1
                                          have p10678_1 := h10678c.2.1
                                          have p10678_2 := h10678c.2.2.1
                                          have p10678_3 := h10678c.2.2.2
                                          linarith only [hlam, p10678_0]
                                      · linarith only [h10677, hlam, p10639_0]
                                    · linarith only [h10676, h9898, hlam]
                                · linarith only [h10673, h9892, hlam]
                              · linarith only [h10672, h9886, hlam]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [h10459, hlam, p10639_0]
                            · have p10639_0 := h10639c.1
                              have p10639_1 := h10639c.2.1
                              have p10639_2 := h10639c.2.2.1
                              have p10639_3 := h10639c.2.2.2
                              linarith only [hlam, p10639_0]
                          · linarith only [h10456, h10638, hlam]
                        · linarith only [h10637, h9898, hlam]
                    · linarith only [h10634, h9892, hlam]
                  · linarith only [h10633, h9886, hlam]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [h10458, hlam, p10580_0]
                · have p10580_0 := h10580c.1
                  have p10580_1 := h10580c.2.1
                  have p10580_2 := h10580c.2.2.1
                  have p10580_3 := h10580c.2.2.2
                  linarith only [hlam, p10580_0]
              · linarith only [h10579, h9666, hlam]
            · linarith only [h10578, h8836, hlam]
          · linarith only [h10577, h7600, hlam]
        · linarith only [h0, h10576, hlam]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h9888, hlam, p10460_1]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h9890, hlam, p10460_0]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [h9891, hlam, p10460_1]
    · have p10460_0 := h10460c.1
      have p10460_1 := h10460c.2.1
      have p10460_2 := h10460c.2.2.1
      have p10460_3 := h10460c.2.2.2
      linarith only [hlam, p10460_0]
  · linarith only [h10458, h10459, h9898, hlam]

end R2N4
