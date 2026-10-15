import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8694 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8695 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8696 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h0 := hg0
  have h6137 := hg6137
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 3 5 (by decide) (by decide) with h8697 | h8697
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8698 | h8698
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8699 | h8699
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8700 | h8700
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8701 | h8701
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8702 | h8702
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8703 | h8703
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8704 | h8704
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8705 | h8705
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8706 | h8706
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8707 | h8707
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8708 | h8708
                        · rcases h1bigk with h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c | h8709c
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [hlam, p8709_0]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h0, hlam, p8709_0]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h6137, hlam, p8709_0]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h7252, hlam, p8709_0]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h8021, hlam, p8709_0]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [hlam, p8709_0]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h7252, hc01, hc12, hlam, hphi, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h8699, hlam, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [hlam, p8709_0]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h7252, h8699, hc01, hc12, hlam, hphi, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h8021, h8699, hc01, hc12, hlam, hphi, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h8700, hlam, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h8702, hlam, p8709_0]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [hlam, p8709_0]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h8021, h8699, h8702, hc01, hc12, hlam, hphi, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h8701, hlam, p8709_1]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h8703, hlam, p8709_0]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [h8704, hlam, p8709_0]
                          · have p8709_0 := h8709c.1
                            have p8709_1 := h8709c.2.1
                            have p8709_2 := h8709c.2.2.1
                            have p8709_3 := h8709c.2.2.2
                            linarith only [hlam, p8709_0]
                        · rcases h1bigk with h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c | h8735c
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [hlam, p8735_0]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h0, hlam, p8735_0]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h6137, hlam, p8735_0]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h7252, hlam, p8735_0]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h8021, hlam, p8735_0]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [hlam, p8735_0]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h7252, hc01, hc12, hlam, hphi, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h8699, hlam, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [hlam, p8735_0]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h7252, h8694, h8699, h8707, h8708, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h8021, h8699, hc01, hc12, hlam, hphi, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h8700, hlam, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h8702, hlam, p8735_0]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [hlam, p8735_0]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h8021, h8699, h8702, hc01, hc12, hlam, hphi, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h8701, hlam, p8735_1]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h8703, hlam, p8735_0]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [h8704, hlam, p8735_0]
                          · have p8735_0 := h8735c.1
                            have p8735_1 := h8735c.2.1
                            have p8735_2 := h8735c.2.2.1
                            have p8735_3 := h8735c.2.2.2
                            linarith only [hlam, p8735_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8761 | h8761
                        · linarith only [h8705, h8707, h8761, hlam]
                        · rcases h1bigk with h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c | h8763c
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [hlam, p8763_0]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h0, hlam, p8763_0]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h6137, hlam, p8763_0]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h7252, hlam, p8763_0]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h8021, hlam, p8763_0]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [hlam, p8763_0]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h7252, hc01, hc12, hlam, hphi, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h8699, hlam, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [hlam, p8763_0]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h7252, h8699, hc01, hc12, hlam, hphi, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h8021, h8699, hc01, hc12, hlam, hphi, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h8700, hlam, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h8702, hlam, p8763_0]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [hlam, p8763_0]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h8021, h8699, h8702, hc01, hc12, hlam, hphi, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h8701, hlam, p8763_1]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h8703, hlam, p8763_0]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [h8704, hlam, p8763_0]
                          · have p8763_0 := h8763c.1
                            have p8763_1 := h8763c.2.1
                            have p8763_2 := h8763c.2.2.1
                            have p8763_3 := h8763c.2.2.2
                            linarith only [hlam, p8763_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8789 | h8789
                      · linarith only [h8705, h8706, h8789, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8791 | h8791
                        · linarith only [h6137, h8697, h8699, h8705, h8706, h8789, h8791, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h1bigk with h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c | h8793c
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [hlam, p8793_0]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h0, hlam, p8793_0]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h6137, hlam, p8793_0]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h7252, hlam, p8793_0]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h8021, hlam, p8793_0]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [hlam, p8793_0]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h7252, h8698, h8702, h8706, h8791, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h7252, h8698, h8706, h8791, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h8699, hlam, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [hlam, p8793_0]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h7252, h8698, h8699, h8706, h8791, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h8021, h8699, hc01, hc12, hlam, hphi, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h8700, hlam, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h8702, hlam, p8793_0]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [hlam, p8793_0]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h8021, h8699, h8702, hc01, hc12, hlam, hphi, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h8701, hlam, p8793_1]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h8703, hlam, p8793_0]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [h8704, hlam, p8793_0]
                          · have p8793_0 := h8793c.1
                            have p8793_1 := h8793c.2.1
                            have p8793_2 := h8793c.2.2.1
                            have p8793_3 := h8793c.2.2.2
                            linarith only [hlam, p8793_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8819 | h8819
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8820 | h8820
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8821 | h8821
                        · rcases h1bigk with h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c | h8822c
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [hlam, p8822_0]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h0, hlam, p8822_0]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h6137, hlam, p8822_0]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h7252, hlam, p8822_0]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h8021, hlam, p8822_0]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [hlam, p8822_0]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h7252, h8696, h8705, h8819, h8821, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h8699, hlam, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [hlam, p8822_0]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h7252, h8696, h8699, h8705, h8819, h8821, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h8021, h8699, hc01, hc12, hlam, hphi, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h8700, hlam, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h8702, hlam, p8822_0]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [hlam, p8822_0]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h8021, h8699, h8702, hc01, hc12, hlam, hphi, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h8701, hlam, p8822_1]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h8703, hlam, p8822_0]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [h8704, hlam, p8822_0]
                          · have p8822_0 := h8822c.1
                            have p8822_1 := h8822c.2.1
                            have p8822_2 := h8822c.2.2.1
                            have p8822_3 := h8822c.2.2.2
                            linarith only [hlam, p8822_0]
                        · linarith only [h8698, h8705, h8819, h8821, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h8705, h8819, h8820, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8850 | h8850
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8851 | h8851
                        · rcases h1bigk with h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c | h8852c
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [hlam, p8852_0]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h0, hlam, p8852_0]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h6137, hlam, p8852_0]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h7252, hlam, p8852_0]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h8021, hlam, p8852_0]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [hlam, p8852_0]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h7252, h8696, h8819, h8851, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h8699, hlam, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [hlam, p8852_0]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h7252, h8699, hc01, hc12, hlam, hphi, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h8021, h8699, hc01, hc12, hlam, hphi, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h8700, hlam, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h8702, hlam, p8852_0]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [hlam, p8852_0]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h8021, h8699, h8702, hc01, hc12, hlam, hphi, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h8701, hlam, p8852_1]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h8703, hlam, p8852_0]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [h8704, hlam, p8852_0]
                          · have p8852_0 := h8852c.1
                            have p8852_1 := h8852c.2.1
                            have p8852_2 := h8852c.2.2.1
                            have p8852_3 := h8852c.2.2.2
                            linarith only [hlam, p8852_0]
                        · linarith only [h0, h8694, h8705, h8850, h8851, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8879 | h8879
                        · rcases h1bigk with h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c | h8880c
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [hlam, p8880_0]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h0, hlam, p8880_0]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h6137, hlam, p8880_0]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h7252, hlam, p8880_0]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h8021, hlam, p8880_0]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [hlam, p8880_0]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h6137, h8696, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h7252, h8698, h8705, h8850, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h8699, hlam, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [hlam, p8880_0]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h7252, h8698, h8699, h8705, h8850, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h8021, h8699, hc01, hc12, hlam, hphi, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h8700, hlam, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h8702, hlam, p8880_0]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [hlam, p8880_0]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h8021, h8699, h8702, hc01, hc12, hlam, hphi, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h8701, hlam, p8880_1]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h8703, hlam, p8880_0]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [h8704, hlam, p8880_0]
                          · have p8880_0 := h8880c.1
                            have p8880_1 := h8880c.2.1
                            have p8880_2 := h8880c.2.2.1
                            have p8880_3 := h8880c.2.2.2
                            linarith only [hlam, p8880_0]
                        · rcases h1bigk with h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c | h8906c
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [hlam, p8906_0]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h0, hlam, p8906_0]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h6137, hlam, p8906_0]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h7252, hlam, p8906_0]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h8021, hlam, p8906_0]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [hlam, p8906_0]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h7252, h8698, h8705, h8879, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h8021, h8698, h8705, h8879, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h8699, hlam, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [hlam, p8906_0]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h7252, h8698, h8699, h8705, h8879, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h8021, h8698, h8699, h8705, h8879, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h8700, hlam, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h8702, hlam, p8906_0]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [hlam, p8906_0]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h8021, h8698, h8699, h8702, h8705, h8879, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h8701, hlam, p8906_1]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h8703, hlam, p8906_0]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [h8704, hlam, p8906_0]
                          · have p8906_0 := h8906c.1
                            have p8906_1 := h8906c.2.1
                            have p8906_2 := h8906c.2.2.1
                            have p8906_3 := h8906c.2.2.2
                            linarith only [hlam, p8906_0]
                · linarith only [h6137, h7252, h8696, h8698, h8699, h8704, hc01, hc12, hlam, hphi]
              · linarith only [h6137, h8697, h8703, hlam]
            · linarith only [h6137, h8696, h8702, hlam]
          · linarith only [h0, h8695, h8701, hlam]
        · linarith only [h0, h8694, h8700, hlam]
      · linarith only [h0, h8693, h8699, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8938 | h8938
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8939 | h8939
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8940 | h8940
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8941 | h8941
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8942 | h8942
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8943 | h8943
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8944 | h8944
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8945 | h8945
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8946 | h8946
                      · linarith only [h8694, h8698, h8946, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8948 | h8948
                        · linarith only [h8694, h8698, h8944, h8948, hlam]
                        · rcases h1bigk with h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c | h8950c
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [hlam, p8950_0]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h0, hlam, p8950_0]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h6137, hlam, p8950_0]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h7252, hlam, p8950_0]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h8021, hlam, p8950_0]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [hlam, p8950_0]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h7252, h8698, h8941, h8943, hc01, hc12, hlam, hphi, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h7252, h8698, h8943, hc01, hc12, hlam, hphi, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h7252, h8698, h8943, hc01, hc12, hlam, hphi, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h8938, hlam, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [hlam, p8950_0]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h7252, h8698, h8938, h8943, hc01, hc12, hlam, hphi, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h7252, h8698, h8938, h8943, hc01, hc12, hlam, hphi, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h8939, hlam, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h8941, hlam, p8950_0]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [hlam, p8950_0]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h7252, h8698, h8938, h8941, h8943, hc01, hc12, hlam, hphi, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h8940, hlam, p8950_1]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h8942, hlam, p8950_0]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [h8943, hlam, p8950_0]
                          · have p8950_0 := h8950c.1
                            have p8950_1 := h8950c.2.1
                            have p8950_2 := h8950c.2.2.1
                            have p8950_3 := h8950c.2.2.2
                            linarith only [hlam, p8950_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8976 | h8976
                      · linarith only [h0, h8694, h8697, h8698, h8944, h8945, h8976, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8978 | h8978
                        · linarith only [h8697, h8698, h8944, h8945, h8978, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c | h8980c
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [hlam, p8980_0]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h0, hlam, p8980_0]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h6137, hlam, p8980_0]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h7252, hlam, p8980_0]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8021, hlam, p8980_0]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [hlam, p8980_0]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8021, h8697, h8943, h8944, h8945, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8021, h8697, h8944, h8945, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8938, hlam, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [hlam, p8980_0]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8021, h8697, h8938, h8943, h8944, h8945, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8021, h8697, h8938, h8944, h8945, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8939, hlam, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8941, hlam, p8980_0]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [hlam, p8980_0]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8021, h8697, h8938, h8941, h8944, h8945, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8940, hlam, p8980_1]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8942, hlam, p8980_0]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [h8943, hlam, p8980_0]
                          · have p8980_0 := h8980c.1
                            have p8980_1 := h8980c.2.1
                            have p8980_2 := h8980c.2.2.1
                            have p8980_3 := h8980c.2.2.2
                            linarith only [hlam, p8980_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9006 | h9006
                    · linarith only [h8696, h8698, h8938, h8941, h8943, h8944, h9006, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9008 | h9008
                      · linarith only [h8696, h8698, h8944, h9008, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9010 | h9010
                        · linarith only [h8696, h8698, h9010, hlam]
                        · rcases h1bigk with h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c | h9012c
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [hlam, p9012_0]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h0, hlam, p9012_0]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h6137, hlam, p9012_0]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h7252, hlam, p9012_0]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8021, hlam, p9012_0]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [hlam, p9012_0]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8698, h8941, h8943, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8696, h8698, h8943, h8944, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8938, hlam, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [hlam, p9012_0]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8696, h8698, h8938, h8943, h8944, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8021, h8938, hc01, hc12, hlam, hphi, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8939, hlam, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8941, hlam, p9012_0]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [hlam, p9012_0]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8021, h8938, h8941, hc01, hc12, hlam, hphi, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8940, hlam, p9012_1]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8942, hlam, p9012_0]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [h8943, hlam, p9012_0]
                          · have p9012_0 := h9012c.1
                            have p9012_1 := h9012c.2.1
                            have p9012_2 := h9012c.2.2.1
                            have p9012_3 := h9012c.2.2.2
                            linarith only [hlam, p9012_0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9038 | h9038
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9039 | h9039
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9040 | h9040
                      · linarith only [h7252, h8694, h8943, h9040, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9042 | h9042
                        · linarith only [h7252, h8694, h8943, h9038, h9042, hlam]
                        · rcases h1bigk with h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c | h9044c
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [hlam, p9044_0]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h0, hlam, p9044_0]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h6137, hlam, p9044_0]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h7252, hlam, p9044_0]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h8021, hlam, p9044_0]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [hlam, p9044_0]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h7252, hc01, hc12, hlam, hphi, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h8938, hlam, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [hlam, p9044_0]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h7252, h8938, hc01, hc12, hlam, hphi, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h7252, h8021, h8698, h8938, hc01, hc12, hlam, hphi, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h8939, hlam, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h8941, hlam, p9044_0]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [hlam, p9044_0]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h8943, hlam, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h8940, hlam, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h8942, hlam, p9044_0]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [h8943, hc14, hc45, hlam, hphi, p9044_1]
                          · have p9044_0 := h9044c.1
                            have p9044_1 := h9044c.2.1
                            have p9044_2 := h9044c.2.2.1
                            have p9044_3 := h9044c.2.2.2
                            linarith only [hlam, p9044_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9070 | h9070
                      · linarith only [h0, h8021, h8694, h8697, h8943, h9038, h9039, h9070, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9072 | h9072
                        · linarith only [h7252, h8697, h8943, h9038, h9039, h9072, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c | h9074c
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [hlam, p9074_0]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h0, hlam, p9074_0]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h6137, hlam, p9074_0]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h7252, hlam, p9074_0]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h8021, hlam, p9074_0]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [hlam, p9074_0]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h7252, hc01, hc12, hlam, hphi, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h8938, hlam, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [hlam, p9074_0]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h7252, h8938, hc01, hc12, hlam, hphi, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h8021, h8697, h8938, h9039, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h8939, hlam, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h8941, hlam, p9074_0]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [hlam, p9074_0]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h8943, hlam, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h8940, hlam, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h8942, hlam, p9074_0]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [h8943, hc14, hc45, hlam, hphi, p9074_1]
                          · have p9074_0 := h9074c.1
                            have p9074_1 := h9074c.2.1
                            have p9074_2 := h9074c.2.2.1
                            have p9074_3 := h9074c.2.2.2
                            linarith only [hlam, p9074_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9100 | h9100
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9101 | h9101
                      · linarith only [h7252, h8696, h8943, h9038, h9101, hlam]
                      · linarith only [h9038, h9100, h9101, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9104 | h9104
                      · linarith only [h7252, h8943, h9104, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9106 | h9106
                        · linarith only [h7252, h8696, h8943, h9106, hlam]
                        · rcases h1bigk with h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c | h9108c
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [hlam, p9108_0]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h0, hlam, p9108_0]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h6137, hlam, p9108_0]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h7252, hlam, p9108_0]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h8021, hlam, p9108_0]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [hlam, p9108_0]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h7252, hc01, hc12, hlam, hphi, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h8938, hlam, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [hlam, p9108_0]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h7252, h8938, hc01, hc12, hlam, hphi, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h8021, h8938, hc01, hc12, hlam, hphi, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h8939, hlam, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h8941, hlam, p9108_0]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [hlam, p9108_0]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h8943, hlam, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h8940, hlam, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h8942, hlam, p9108_0]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [h7252, h8943, hc04, hc45, hlam, hphi, p9108_1]
                          · have p9108_0 := h9108c.1
                            have p9108_1 := h9108c.2.1
                            have p9108_2 := h9108c.2.2.1
                            have p9108_3 := h9108c.2.2.2
                            linarith only [hlam, p9108_0]
              · linarith only [h6137, h8697, h8942, hlam]
            · linarith only [h6137, h8696, h8941, hlam]
          · linarith only [h0, h8693, h8695, h8697, h8940, hlam]
        · linarith only [h0, h8694, h8939, hlam]
      · linarith only [h0, h8693, h8938, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9139 | h9139
    · linarith only [h8696, h8697, h9139, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9141 | h9141
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9142 | h9142
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9143 | h9143
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9144 | h9144
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9145 | h9145
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9146 | h9146
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9147 | h9147
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9148 | h9148
                    · linarith only [h8693, h8697, h9148, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9150 | h9150
                      · linarith only [h8694, h9139, h9150, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9152 | h9152
                        · linarith only [h8693, h8697, h9139, h9141, h9145, h9147, h9152, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h1bigk with h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c | h9154c
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [hlam, p9154_0]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h0, hlam, p9154_0]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h6137, hlam, p9154_0]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h7252, hlam, p9154_0]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h8021, hlam, p9154_0]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [hlam, p9154_0]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h8697, h9144, h9146, h9152, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h8693, h8697, h9146, h9147, h9152, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h8693, h8697, h9146, h9147, h9152, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h9141, hlam, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [hlam, p9154_0]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h8693, h8697, h9141, h9146, h9147, h9152, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h8693, h8697, h9141, h9146, h9147, h9152, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h9142, hlam, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h9144, hlam, p9154_0]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [hlam, p9154_0]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h8693, h8697, h9141, h9144, h9146, h9147, h9152, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h9143, hlam, p9154_1]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h9145, hlam, p9154_0]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [h9146, hlam, p9154_0]
                          · have p9154_0 := h9154c.1
                            have p9154_1 := h9154c.2.1
                            have p9154_2 := h9154c.2.2.1
                            have p9154_3 := h9154c.2.2.2
                            linarith only [hlam, p9154_0]
                  · linarith only [h8696, h8697, h9147, hc23, hc35, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9181 | h9181
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9182 | h9182
                    · linarith only [h8693, h8697, h9182, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9184 | h9184
                      · linarith only [h7252, h9146, h9184, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9186 | h9186
                        · linarith only [h7252, h9146, h9186, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h1bigk with h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c | h9188c
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [hlam, p9188_0]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h0, hlam, p9188_0]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h6137, hlam, p9188_0]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h7252, hlam, p9188_0]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h8021, hlam, p9188_0]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [hlam, p9188_0]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h8697, h9145, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h7252, hc01, hc12, hlam, hphi, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h9141, hlam, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [hlam, p9188_0]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h7252, h9141, hc01, hc12, hlam, hphi, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h8021, h9141, hc01, hc12, hlam, hphi, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h9142, hlam, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h9144, hlam, p9188_0]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [hlam, p9188_0]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h9146, hlam, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h9143, hlam, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h9145, hlam, p9188_0]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [h9146, hc14, hc45, hlam, hphi, p9188_1]
                          · have p9188_0 := h9188c.1
                            have p9188_1 := h9188c.2.1
                            have p9188_2 := h9188c.2.2.1
                            have p9188_3 := h9188c.2.2.2
                            linarith only [hlam, p9188_0]
                  · linarith only [h8696, h8697, h9181, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9215 | h9215
                · linarith only [h7252, h9139, h9144, h9145, h9215, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9217 | h9217
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9218 | h9218
                    · linarith only [h6137, h9145, h9218, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9220 | h9220
                      · linarith only [h0, h8021, h8694, h9215, h9220, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9222 | h9222
                        · linarith only [h7252, h9215, h9222, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h1bigk with h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c | h9224c
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [hlam, p9224_0]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h0, hlam, p9224_0]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h6137, hlam, p9224_0]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h7252, hlam, p9224_0]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h8021, hlam, p9224_0]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [hlam, p9224_0]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h7252, h9144, hc01, hc12, hlam, hphi, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h7252, hc01, hc12, hlam, hphi, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h7252, h9144, h9145, hc01, hc12, hlam, hphi, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h9141, hlam, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [hlam, p9224_0]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h9145, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h9145, hlam, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h9142, hlam, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h9144, hlam, p9224_0]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [hlam, p9224_0]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h9215, hlam, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h9143, hlam, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h6137, h9145, h9222, hc03, hc45, hlam, hphi, ht34, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [h7252, h9145, h9222, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9224_1]
                          · have p9224_0 := h9224c.1
                            have p9224_1 := h9224c.2.1
                            have p9224_2 := h9224c.2.2.1
                            have p9224_3 := h9224c.2.2.2
                            linarith only [hlam, p9224_0]
                  · linarith only [h8696, h8697, h9217, hc23, hc35, hlam, hphi]
            · linarith only [h6137, h8696, h9144, hlam]
          · linarith only [h0, h8695, h9143, hlam]
        · linarith only [h0, h8694, h8696, h8697, h9142, hc01, hc35, hlam, hphi, ht12, ht23]
      · linarith only [h0, h8693, h9141, hlam]

end R2N4
