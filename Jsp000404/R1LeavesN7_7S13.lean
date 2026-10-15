import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h8520 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 0 4 5 (by decide) (by decide) with h8521 | h8521
  · rcases m.htr 1 2 3 (by decide) (by decide) with h8522 | h8522
    · linarith only [h0, h4, h8520, h8522, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8524 | h8524
      · linarith only [h0, h5543, h8524, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8526 | h8526
        · linarith only [h0, h6343, h8526, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8528 | h8528
          · linarith only [h6418, h8520, h8528, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8530 | h8530
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8531 | h8531
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8532 | h8532
                · linarith only [h1, h6418, h8530, h8532, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8534 | h8534
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8535 | h8535
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8536 | h8536
                      · rcases h1bigk with h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c | h8537c
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          rcases p8537_3 (m.d 0 1) (by simp) with h8539 | h8539
                          · rcases p8537_3 (m.d 1 2) (by simp) with h8540 | h8540
                            · linarith only [h8540, hlam, p8537_0]
                            · rcases p8537_3 (m.d 1 3) (by simp) with h8542 | h8542
                              · linarith only [h1, h8542, hlam]
                              · linarith only [h8522, h8542, hlam]
                          · linarith only [h8539, hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h8530, h8536, hc01, hlam, hphi, ht0b, ht5b, p8537_1, u5ehi4]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h8528, h8530, h8536, hc01, hlam, hphi, ht0b, ht5b, p8537_1, u5ehi4]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          rcases p8537_3 (m.d 0 1) (by simp) with h8548 | h8548
                          · rcases p8537_3 (m.d 1 2) (by simp) with h8549 | h8549
                            · linarith only [h0, h8549, hlam]
                            · rcases p8537_3 (m.d 1 3) (by simp) with h8551 | h8551
                              · linarith only [h1, h8551, hlam]
                              · linarith only [h8530, h8551, hlam]
                          · linarith only [h8548, hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h0, hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h8522, hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h8524, hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h8526, hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h1, hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h1, h4, h8532, hc12, hc34, hlam, hphi, ht23, p8537_1]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h8528, hlam, p8537_1]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h1, h4, h8530, h8532, h8536, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8537_1, u5ehi4]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h2, hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          rcases p8537_3 (m.d 0 1) (by simp) with h8566 | h8566
                          · rcases p8537_3 (m.d 1 2) (by simp) with h8567 | h8567
                            · linarith only [h8524, h8567, hlam]
                            · rcases p8537_3 (m.d 1 3) (by simp) with h8569 | h8569
                              · linarith only [h8528, h8569, hlam]
                              · linarith only [h8522, h8569, hlam]
                          · linarith only [h0, h8566, hlam]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h2, h8530, h8536, hc04, hlam, hphi, ht0b, ht5b, p8537_1, u5ehi4]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h2, h8530, h8536, hc01, hlam, hphi, ht0b, ht5b, p8537_1, u5ehi4]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h3, hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h3, h6343, h8532, h8534, hc12, hc34, hlam, hphi, ht23, p8537_1]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h8530, hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [h8531, hlam, p8537_0]
                        · have p8537_0 := h8537c.1
                          have p8537_1 := h8537c.2.1
                          have p8537_2 := h8537c.2.2.1
                          have p8537_3 := h8537c.2.2.2
                          linarith only [hlam, p8537_0]
                      · linarith only [h6343, h8532, h8534, h8536, hc02, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h3, h5543, h6343, h8531, h8532, h8534, h8535, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h4, h8530, h8534, hlam]
              · linarith only [h8521, h8528, h8530, h8531, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
            · linarith only [h6418, h8520, h8530, hc13, hc34, hlam, hphi]
  · linarith only [h6418, h8520, h8521, hlam]

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h8520 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h8587 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 1 2 3 (by decide) (by decide) with h8588 | h8588
  · linarith only [h0, h4, h8588, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h8590 | h8590
    · linarith only [h0, h5543, h8590, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h8592 | h8592
      · linarith only [h1, h6343, h8520, h8588, h8592, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h8594 | h8594
        · linarith only [h1, h6418, h8594, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h8596 | h8596
          · linarith only [h1, h8520, h8596, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8598 | h8598
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8599 | h8599
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8600 | h8600
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8601 | h8601
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8602 | h8602
                    · rcases h1bigk with h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c | h8603c
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        rcases p8603_3 (m.d 0 1) (by simp) with h8605 | h8605
                        · rcases p8603_3 (m.d 1 2) (by simp) with h8606 | h8606
                          · linarith only [h8606, hlam, p8603_0]
                          · rcases p8603_3 (m.d 1 3) (by simp) with h8608 | h8608
                            · linarith only [h1, h8608, hlam]
                            · linarith only [h8588, h8608, hlam]
                        · linarith only [h8605, hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        rcases p8603_3 (m.d 0 1) (by simp) with h8612 | h8612
                        · rcases p8603_3 (m.d 1 2) (by simp) with h8613 | h8613
                          · linarith only [h0, h8613, hlam]
                          · rcases p8603_3 (m.d 1 3) (by simp) with h8615 | h8615
                            · linarith only [h8615, hlam, p8603_0]
                            · rcases p8603_3 (m.d 1 4) (by simp) with h8617 | h8617
                              · linarith only [h2, h8617, hlam]
                              · linarith only [h8594, h8617, hlam]
                        · linarith only [h8612, hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h8598, hc01, hlam, hphi, ht0b, ht5b, p8603_1, u5ehi4]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        rcases p8603_3 (m.d 0 1) (by simp) with h8622 | h8622
                        · rcases p8603_3 (m.d 1 2) (by simp) with h8623 | h8623
                          · linarith only [h0, h8623, hlam]
                          · rcases p8603_3 (m.d 1 3) (by simp) with h8625 | h8625
                            · linarith only [h1, h8625, hlam]
                            · rcases p8603_3 (m.d 1 4) (by simp) with h8627 | h8627
                              · linarith only [h2, h8627, hlam]
                              · linarith only [h8598, h8627, hlam]
                        · linarith only [h8622, hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h0, hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h8588, hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h8590, hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h8592, hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h1, hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h1, h8520, h8599, h8602, hc12, hc23, hlam, hphi, p8603_1]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h8594, hlam, p8603_1]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h8596, hlam, p8603_1]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h2, hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h2, h6418, h8599, hc12, hc23, hlam, hphi, p8603_1]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h2, h6418, h8588, h8599, hc12, hc23, hlam, hphi, p8603_1]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h2, h6418, h8599, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8603_1, u5ehi1]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h3, hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h3, h8520, h8599, h8602, hc12, hc23, hlam, hphi, p8603_1]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h3, h8520, h8588, h8599, h8602, hc12, hc23, hlam, hphi, p8603_1]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [h8598, hlam, p8603_0]
                      · have p8603_0 := h8603c.1
                        have p8603_1 := h8603c.2.1
                        have p8603_2 := h8603c.2.2.1
                        have p8603_3 := h8603c.2.2.2
                        linarith only [hlam, p8603_0]
                    · linarith only [h6418, h8587, h8602, hlam]
                  · linarith only [h2, h6418, h8598, h8599, h8601, hlam]
                · linarith only [h2, h6418, h8598, h8599, h8600, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8654 | h8654
                · linarith only [h8520, h8599, h8654, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8656 | h8656
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8657 | h8657
                    · rcases h1bigk with h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c | h8658c
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        rcases p8658_3 (m.d 0 1) (by simp) with h8660 | h8660
                        · rcases p8658_3 (m.d 1 2) (by simp) with h8661 | h8661
                          · linarith only [h8661, hlam, p8658_0]
                          · rcases p8658_3 (m.d 1 3) (by simp) with h8663 | h8663
                            · linarith only [h1, h8663, hlam]
                            · linarith only [h8588, h8663, hlam]
                        · linarith only [h8660, hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        rcases p8658_3 (m.d 0 1) (by simp) with h8667 | h8667
                        · rcases p8658_3 (m.d 1 2) (by simp) with h8668 | h8668
                          · linarith only [h0, h8668, hlam]
                          · rcases p8658_3 (m.d 1 3) (by simp) with h8670 | h8670
                            · linarith only [h8670, hlam, p8658_0]
                            · rcases p8658_3 (m.d 1 4) (by simp) with h8672 | h8672
                              · linarith only [h2, h8672, hlam]
                              · linarith only [h8594, h8672, hlam]
                        · linarith only [h8667, hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h8598, hc01, hlam, hphi, ht0b, ht5b, p8658_1, u5ehi4]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        rcases p8658_3 (m.d 0 1) (by simp) with h8677 | h8677
                        · rcases p8658_3 (m.d 1 2) (by simp) with h8678 | h8678
                          · linarith only [h0, h8678, hlam]
                          · rcases p8658_3 (m.d 1 3) (by simp) with h8680 | h8680
                            · linarith only [h1, h8680, hlam]
                            · rcases p8658_3 (m.d 1 4) (by simp) with h8682 | h8682
                              · linarith only [h2, h8682, hlam]
                              · linarith only [h8598, h8682, hlam]
                        · linarith only [h8677, hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h0, hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h8588, hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h8590, hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h8592, hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h1, hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h1, h4, h8654, h8657, hc12, hc34, hlam, hphi, ht23, p8658_1]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h8594, hlam, p8658_1]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h8596, hlam, p8658_1]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h2, hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        rcases p8658_3 (m.d 0 1) (by simp) with h8697 | h8697
                        · rcases p8658_3 (m.d 1 2) (by simp) with h8698 | h8698
                          · linarith only [h8590, h8698, hlam]
                          · rcases p8658_3 (m.d 1 3) (by simp) with h8700 | h8700
                            · linarith only [h8594, h8700, hlam]
                            · linarith only [h8588, h8700, hlam]
                        · linarith only [h0, h8697, hlam]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        rcases p8658_3 (m.d 0 1) (by simp) with h8704 | h8704
                        · rcases p8658_3 (m.d 1 2) (by simp) with h8705 | h8705
                          · linarith only [h8590, h8705, hlam]
                          · rcases p8658_3 (m.d 1 3) (by simp) with h8707 | h8707
                            · linarith only [h8594, h8707, hlam]
                            · rcases p8658_3 (m.d 1 4) (by simp) with h8709 | h8709
                              · rcases p8658_3 (m.d 1 5) (by simp) with h8710 | h8710
                                · linarith only [h8598, h8710, hlam]
                                · linarith only [h8596, h8710, hlam]
                              · linarith only [h8594, h8709, hlam]
                        · linarith only [h1, h8704, hlam]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p8658_1, u5ehi1]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h3, hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        rcases p8658_3 (m.d 0 1) (by simp) with h8718 | h8718
                        · rcases p8658_3 (m.d 1 2) (by simp) with h8719 | h8719
                          · linarith only [h8592, h8719, hlam]
                          · rcases p8658_3 (m.d 1 3) (by simp) with h8721 | h8721
                            · linarith only [h8596, h8721, hlam]
                            · linarith only [h8588, h8721, hlam]
                        · linarith only [h0, h8718, hlam]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        rcases p8658_3 (m.d 0 1) (by simp) with h8725 | h8725
                        · rcases p8658_3 (m.d 1 2) (by simp) with h8726 | h8726
                          · linarith only [h8592, h8726, hlam]
                          · rcases p8658_3 (m.d 1 3) (by simp) with h8728 | h8728
                            · linarith only [h8596, h8728, hlam]
                            · rcases p8658_3 (m.d 1 4) (by simp) with h8730 | h8730
                              · rcases p8658_3 (m.d 1 5) (by simp) with h8731 | h8731
                                · rcases h1emax with h8732 | h8732 | h8732 | h8732 | h8732
                                  · linarith only [h2, h8598, h8732, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                  · rcases h3bigk with h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c | h8734c
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h4, h8588, h8654, h8657, hc12, hc34, hlam, hphi, ht23, p8734_1]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h4, hlam, p8734_1]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h6418, hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h8520, hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h1, hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h8588, hlam, p8734_1]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h8594, hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h8596, hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h8654, h8657, hc03, hc34, hlam, hphi, p8734_1]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h8588, h8654, h8657, hc12, hc34, hlam, hphi, ht23, p8734_1]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h8599, hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h8654, hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      rcases p8734_3 (m.d 0 3) (by simp) with h8750 | h8750
                                      · linarith only [h8750, hlam, p8734_0]
                                      · rcases p8734_3 (m.d 1 3) (by simp) with h8752 | h8752
                                        · linarith only [h8594, h8752, hlam]
                                        · rcases p8734_3 (m.d 2 3) (by simp) with h8754 | h8754
                                          · linarith only [h8599, h8754, hlam]
                                          · linarith only [h4, h8754, hlam]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      rcases p8734_3 (m.d 0 3) (by simp) with h8757 | h8757
                                      · linarith only [h6418, h8757, hlam]
                                      · linarith only [h1, h8757, hlam]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p8734_1]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h1, h8520, h8588, hc12, hc34, hlam, hphi, ht23, p8734_1]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      rcases p8734_3 (m.d 0 3) (by simp) with h8763 | h8763
                                      · linarith only [h8763, hlam, p8734_0]
                                      · rcases p8734_3 (m.d 1 3) (by simp) with h8765 | h8765
                                        · linarith only [h8596, h8765, hlam]
                                        · rcases p8734_3 (m.d 2 3) (by simp) with h8767 | h8767
                                          · linarith only [h8654, h8767, hlam]
                                          · linarith only [h4, h8767, hlam]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      rcases p8734_3 (m.d 0 3) (by simp) with h8770 | h8770
                                      · linarith only [h8520, h8770, hlam]
                                      · linarith only [h1, h8770, hlam]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p8734_1]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [h8657, hlam, p8734_0]
                                    · have p8734_0 := h8734c.1
                                      have p8734_1 := h8734c.2.1
                                      have p8734_2 := h8734c.2.2.1
                                      have p8734_3 := h8734c.2.2.2
                                      linarith only [hlam, p8734_0]
                                  · rcases h3bigk with h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c | h8776c
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h6418, h8588, hc12, hc34, hlam, hphi, ht23, p8776_1]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h4, hlam, p8776_1]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h6418, hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h8520, hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h1, hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h8588, hlam, p8776_1]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h8594, hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h8596, hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h8599, hc03, hc34, hlam, hphi, p8776_1]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h8588, h8599, hc12, hc34, hlam, hphi, ht23, p8776_1]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h8599, hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h8654, hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      rcases p8776_3 (m.d 0 3) (by simp) with h8792 | h8792
                                      · linarith only [h8792, hlam, p8776_0]
                                      · rcases p8776_3 (m.d 1 3) (by simp) with h8794 | h8794
                                        · linarith only [h8594, h8794, hlam]
                                        · rcases p8776_3 (m.d 2 3) (by simp) with h8796 | h8796
                                          · linarith only [h8599, h8796, hlam]
                                          · linarith only [h4, h8796, hlam]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      rcases p8776_3 (m.d 0 3) (by simp) with h8799 | h8799
                                      · linarith only [h6418, h8799, hlam]
                                      · linarith only [h1, h8799, hlam]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p8776_1]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h1, h8520, h8588, hc12, hc34, hlam, hphi, ht23, p8776_1]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      rcases p8776_3 (m.d 0 3) (by simp) with h8805 | h8805
                                      · linarith only [h8805, hlam, p8776_0]
                                      · rcases p8776_3 (m.d 1 3) (by simp) with h8807 | h8807
                                        · linarith only [h8596, h8807, hlam]
                                        · rcases p8776_3 (m.d 2 3) (by simp) with h8809 | h8809
                                          · linarith only [h8654, h8809, hlam]
                                          · linarith only [h4, h8809, hlam]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      rcases p8776_3 (m.d 0 3) (by simp) with h8812 | h8812
                                      · linarith only [h8520, h8812, hlam]
                                      · linarith only [h1, h8812, hlam]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p8776_1]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [h8657, hlam, p8776_0]
                                    · have p8776_0 := h8776c.1
                                      have p8776_1 := h8776c.2.1
                                      have p8776_2 := h8776c.2.2.1
                                      have p8776_3 := h8776c.2.2.2
                                      linarith only [hlam, p8776_0]
                                  · linarith only [h8588, h8598, h8732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p8658_1]
                                  · linarith only [h8588, h8732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p8658_1]
                                · linarith only [h8596, h8731, hlam]
                              · linarith only [h8594, h8730, hlam]
                        · linarith only [h1, h8725, hlam]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [h8598, hlam, p8658_0]
                      · have p8658_0 := h8658c.1
                        have p8658_1 := h8658c.2.1
                        have p8658_2 := h8658c.2.2.1
                        have p8658_3 := h8658c.2.2.2
                        linarith only [hlam, p8658_0]
                    · linarith only [h6418, h8587, h8657, hlam]
                  · linarith only [h2, h5543, h8598, h8656, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8827 | h8827
              · linarith only [h6418, h8587, h8588, h8594, h8598, h8827, hc12, hc23, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8829 | h8829
                · linarith only [h1, h8520, h8588, h8827, h8829, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8831 | h8831
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8832 | h8832
                    · rcases h1bigk with h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c | h8833c
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        rcases p8833_3 (m.d 0 1) (by simp) with h8835 | h8835
                        · rcases p8833_3 (m.d 1 2) (by simp) with h8836 | h8836
                          · linarith only [h8836, hlam, p8833_0]
                          · rcases p8833_3 (m.d 1 3) (by simp) with h8838 | h8838
                            · linarith only [h1, h8838, hlam]
                            · linarith only [h8588, h8838, hlam]
                        · linarith only [h8835, hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        rcases p8833_3 (m.d 0 1) (by simp) with h8842 | h8842
                        · rcases p8833_3 (m.d 1 2) (by simp) with h8843 | h8843
                          · linarith only [h0, h8843, hlam]
                          · rcases p8833_3 (m.d 1 3) (by simp) with h8845 | h8845
                            · linarith only [h8845, hlam, p8833_0]
                            · rcases p8833_3 (m.d 1 4) (by simp) with h8847 | h8847
                              · linarith only [h2, h8847, hlam]
                              · linarith only [h8594, h8847, hlam]
                        · linarith only [h8842, hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        rcases p8833_3 (m.d 0 1) (by simp) with h8851 | h8851
                        · rcases p8833_3 (m.d 1 2) (by simp) with h8852 | h8852
                          · linarith only [h0, h8852, hlam]
                          · rcases p8833_3 (m.d 1 3) (by simp) with h8854 | h8854
                            · linarith only [h1, h8854, hlam]
                            · rcases p8833_3 (m.d 1 4) (by simp) with h8856 | h8856
                              · linarith only [h8856, hlam, p8833_0]
                              · rcases p8833_3 (m.d 1 5) (by simp) with h8858 | h8858
                                · linarith only [h3, h8858, hlam]
                                · linarith only [h8598, h8858, hlam]
                        · linarith only [h8851, hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        rcases p8833_3 (m.d 0 1) (by simp) with h8862 | h8862
                        · rcases p8833_3 (m.d 1 2) (by simp) with h8863 | h8863
                          · linarith only [h0, h8863, hlam]
                          · rcases p8833_3 (m.d 1 3) (by simp) with h8865 | h8865
                            · linarith only [h1, h8865, hlam]
                            · rcases p8833_3 (m.d 1 4) (by simp) with h8867 | h8867
                              · linarith only [h2, h8867, hlam]
                              · rcases p8833_3 (m.d 1 5) (by simp) with h8869 | h8869
                                · linarith only [h8869, hlam, p8833_0]
                                · rcases h1emax with h8871 | h8871 | h8871 | h8871 | h8871
                                  · linarith only [h8871, hlam, hphi, ht01, ht0b, ht5b, p8833_1, u5ehi1]
                                  · rcases h3bigk with h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c | h8873c
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h4, h8588, h8829, h8832, hc12, hc34, hlam, hphi, ht23, p8873_1]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h4, hlam, p8873_1]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h6418, hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h8520, hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h1, hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h8588, hlam, p8873_1]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h8594, hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h8596, hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h8829, h8832, hc03, hc34, hlam, hphi, p8873_1]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h8588, h8829, h8832, hc12, hc34, hlam, hphi, ht23, p8873_1]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h8827, hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h8829, hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      rcases p8873_3 (m.d 0 3) (by simp) with h8889 | h8889
                                      · linarith only [h8889, hlam, p8873_0]
                                      · rcases p8873_3 (m.d 1 3) (by simp) with h8891 | h8891
                                        · linarith only [h8594, h8891, hlam]
                                        · rcases p8873_3 (m.d 2 3) (by simp) with h8893 | h8893
                                          · linarith only [h8827, h8893, hlam]
                                          · linarith only [h4, h8893, hlam]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      rcases p8873_3 (m.d 0 3) (by simp) with h8896 | h8896
                                      · linarith only [h6418, h8896, hlam]
                                      · linarith only [h1, h8896, hlam]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p8873_1]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h1, h8520, h8588, hc12, hc34, hlam, hphi, ht23, p8873_1]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      rcases p8873_3 (m.d 0 3) (by simp) with h8902 | h8902
                                      · linarith only [h8902, hlam, p8873_0]
                                      · rcases p8873_3 (m.d 1 3) (by simp) with h8904 | h8904
                                        · linarith only [h8596, h8904, hlam]
                                        · rcases p8873_3 (m.d 2 3) (by simp) with h8906 | h8906
                                          · linarith only [h8829, h8906, hlam]
                                          · linarith only [h4, h8906, hlam]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      rcases p8873_3 (m.d 0 3) (by simp) with h8909 | h8909
                                      · linarith only [h8520, h8909, hlam]
                                      · linarith only [h1, h8909, hlam]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p8873_1]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [h8832, hlam, p8873_0]
                                    · have p8873_0 := h8873c.1
                                      have p8873_1 := h8873c.2.1
                                      have p8873_2 := h8873c.2.2.1
                                      have p8873_3 := h8873c.2.2.2
                                      linarith only [hlam, p8873_0]
                                  · rcases h3bigk with h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c | h8915c
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h6418, h8588, hc12, hc34, hlam, hphi, ht23, p8915_1]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h4, hlam, p8915_1]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h6418, hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h8520, hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h1, hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h8588, hlam, p8915_1]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h8594, hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h8596, hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h8827, hc03, hc34, hlam, hphi, p8915_1]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h8588, h8827, hc12, hc34, hlam, hphi, ht23, p8915_1]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h8827, hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h8829, hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      rcases p8915_3 (m.d 0 3) (by simp) with h8931 | h8931
                                      · linarith only [h8931, hlam, p8915_0]
                                      · rcases p8915_3 (m.d 1 3) (by simp) with h8933 | h8933
                                        · linarith only [h8594, h8933, hlam]
                                        · rcases p8915_3 (m.d 2 3) (by simp) with h8935 | h8935
                                          · linarith only [h8827, h8935, hlam]
                                          · linarith only [h4, h8935, hlam]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      rcases p8915_3 (m.d 0 3) (by simp) with h8938 | h8938
                                      · linarith only [h6418, h8938, hlam]
                                      · linarith only [h1, h8938, hlam]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p8915_1]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h1, h8520, h8588, hc12, hc34, hlam, hphi, ht23, p8915_1]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      rcases p8915_3 (m.d 0 3) (by simp) with h8944 | h8944
                                      · linarith only [h8944, hlam, p8915_0]
                                      · rcases p8915_3 (m.d 1 3) (by simp) with h8946 | h8946
                                        · linarith only [h8596, h8946, hlam]
                                        · rcases p8915_3 (m.d 2 3) (by simp) with h8948 | h8948
                                          · linarith only [h8829, h8948, hlam]
                                          · linarith only [h4, h8948, hlam]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      rcases p8915_3 (m.d 0 3) (by simp) with h8951 | h8951
                                      · linarith only [h8520, h8951, hlam]
                                      · linarith only [h1, h8951, hlam]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p8915_1]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [h8832, hlam, p8915_0]
                                    · have p8915_0 := h8915c.1
                                      have p8915_1 := h8915c.2.1
                                      have p8915_2 := h8915c.2.2.1
                                      have p8915_3 := h8915c.2.2.2
                                      linarith only [hlam, p8915_0]
                                  · rcases h3bigk with h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c | h8957c
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h6418, h8588, hc12, hc34, hlam, hphi, ht23, p8957_1]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h4, hlam, p8957_1]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h6418, hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h8520, hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h1, hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h8588, hlam, p8957_1]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h8594, hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h8596, hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h8827, hc03, hc34, hlam, hphi, p8957_1]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h8588, h8827, hc12, hc34, hlam, hphi, ht23, p8957_1]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h8827, hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h8829, hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      rcases p8957_3 (m.d 0 3) (by simp) with h8973 | h8973
                                      · linarith only [h8973, hlam, p8957_0]
                                      · rcases p8957_3 (m.d 1 3) (by simp) with h8975 | h8975
                                        · linarith only [h8594, h8975, hlam]
                                        · rcases p8957_3 (m.d 2 3) (by simp) with h8977 | h8977
                                          · linarith only [h8827, h8977, hlam]
                                          · linarith only [h4, h8977, hlam]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      rcases p8957_3 (m.d 0 3) (by simp) with h8980 | h8980
                                      · linarith only [h6418, h8980, hlam]
                                      · linarith only [h1, h8980, hlam]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p8957_1]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h1, h8520, h8588, hc12, hc34, hlam, hphi, ht23, p8957_1]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      rcases p8957_3 (m.d 0 3) (by simp) with h8986 | h8986
                                      · linarith only [h8986, hlam, p8957_0]
                                      · rcases p8957_3 (m.d 1 3) (by simp) with h8988 | h8988
                                        · linarith only [h8596, h8988, hlam]
                                        · rcases p8957_3 (m.d 2 3) (by simp) with h8990 | h8990
                                          · linarith only [h8829, h8990, hlam]
                                          · linarith only [h4, h8990, hlam]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      rcases p8957_3 (m.d 0 3) (by simp) with h8993 | h8993
                                      · linarith only [h8520, h8993, hlam]
                                      · linarith only [h1, h8993, hlam]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p8957_1]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [h8832, hlam, p8957_0]
                                    · have p8957_0 := h8957c.1
                                      have p8957_1 := h8957c.2.1
                                      have p8957_2 := h8957c.2.2.1
                                      have p8957_3 := h8957c.2.2.2
                                      linarith only [hlam, p8957_0]
                                  · rcases h3bigk with h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c | h8999c
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h6418, h8588, hc12, hc34, hlam, hphi, ht23, p8999_1]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h4, hlam, p8999_1]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h6418, hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h8520, hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h1, hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h8588, hlam, p8999_1]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h8594, hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h8596, hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h8827, hc03, hc34, hlam, hphi, p8999_1]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h8588, h8827, hc12, hc34, hlam, hphi, ht23, p8999_1]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h8827, hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h8829, hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      rcases p8999_3 (m.d 0 3) (by simp) with h9015 | h9015
                                      · linarith only [h9015, hlam, p8999_0]
                                      · rcases p8999_3 (m.d 1 3) (by simp) with h9017 | h9017
                                        · linarith only [h8594, h9017, hlam]
                                        · rcases p8999_3 (m.d 2 3) (by simp) with h9019 | h9019
                                          · linarith only [h8827, h9019, hlam]
                                          · linarith only [h4, h9019, hlam]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      rcases p8999_3 (m.d 0 3) (by simp) with h9022 | h9022
                                      · linarith only [h6418, h9022, hlam]
                                      · linarith only [h1, h9022, hlam]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p8999_1]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h1, h8520, h8588, hc12, hc34, hlam, hphi, ht23, p8999_1]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      rcases p8999_3 (m.d 0 3) (by simp) with h9028 | h9028
                                      · linarith only [h9028, hlam, p8999_0]
                                      · rcases p8999_3 (m.d 1 3) (by simp) with h9030 | h9030
                                        · linarith only [h8596, h9030, hlam]
                                        · rcases p8999_3 (m.d 2 3) (by simp) with h9032 | h9032
                                          · linarith only [h8829, h9032, hlam]
                                          · linarith only [h4, h9032, hlam]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      rcases p8999_3 (m.d 0 3) (by simp) with h9035 | h9035
                                      · linarith only [h8520, h9035, hlam]
                                      · linarith only [h1, h9035, hlam]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p8999_1]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [h8832, hlam, p8999_0]
                                    · have p8999_0 := h8999c.1
                                      have p8999_1 := h8999c.2.1
                                      have p8999_2 := h8999c.2.2.1
                                      have p8999_3 := h8999c.2.2.2
                                      linarith only [hlam, p8999_0]
                        · linarith only [h8862, hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h0, hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h8588, hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h8590, hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h8592, hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h1, hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h8587, h8594, h8598, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8833_1]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h8594, hlam, p8833_1]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h8596, hlam, p8833_1]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h2, hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h6418, h8587, h8598, hc12, hc34, hlam, hphi, ht23, p8833_1]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h6418, h8587, h8598, hc13, hc34, hlam, hphi, p8833_1]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h8598, hlam, p8833_1]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h3, hlam, p8833_0]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h6418, h8587, h8598, hc12, hc34, hlam, hphi, ht23, p8833_1]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h6418, h8587, h8588, h8598, hc12, hc34, hlam, hphi, ht23, p8833_1]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [h6418, h8587, h8590, h8598, hc12, hc34, hlam, hphi, ht23, p8833_1]
                      · have p8833_0 := h8833c.1
                        have p8833_1 := h8833c.2.1
                        have p8833_2 := h8833c.2.2.1
                        have p8833_3 := h8833c.2.2.2
                        linarith only [hlam, p8833_0]
                    · linarith only [h5543, h8587, h8827, h8832, hlam]
                  · linarith only [h5543, h8587, h8831, hlam]

end R2N4
