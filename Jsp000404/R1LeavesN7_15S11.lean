import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8736 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8737 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8738 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0bigk := hb0.1
  have h0 := hg0
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 3 5 (by decide) (by decide) with h8739 | h8739
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8740 | h8740
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8741 | h8741
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8742 | h8742
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8743 | h8743
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8744 | h8744
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8745 | h8745
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8746 | h8746
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8747 | h8747
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8748 | h8748
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8749 | h8749
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8750 | h8750
                        · rcases h0bigk with h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c | h8751c
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [hlam, p8751_0]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h0, hlam, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h6253, hlam, p8751_0]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h7338, hlam, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h8081, hlam, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [hlam, p8751_0]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h0, h8081, h8740, hc01, hc12, hlam, hphi, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h6253, h8741, hc01, hc12, hlam, hphi, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h8735, hlam, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [hlam, p8751_0]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h6253, h7338, h8741, hc01, hc12, hlam, hphi, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h6253, h8081, h8741, hc01, hc12, hlam, hphi, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h7338, h8741, h8744, hc01, hc12, hlam, hphi, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h8736, hlam, p8751_0]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h8738, hlam, p8751_0]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [hlam, p8751_0]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h7338, h8081, h8741, h8744, hc01, hc12, hlam, hphi, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h8081, hc01, hc15, hlam, hphi, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h8737, hlam, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h8739, hlam, p8751_0]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [h8740, hlam, p8751_1]
                          · have p8751_0 := h8751c.1
                            have p8751_1 := h8751c.2.1
                            have p8751_2 := h8751c.2.2.1
                            have p8751_3 := h8751c.2.2.2
                            linarith only [hlam, p8751_0]
                        · rcases h0bigk with h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c | h8777c
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [hlam, p8777_0]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h0, hlam, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h6253, hlam, p8777_0]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h7338, hlam, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h8081, hlam, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [hlam, p8777_0]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h6253, h8741, hc01, hc12, hlam, hphi, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h8735, hlam, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [hlam, p8777_0]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h6253, h8736, h8741, h8749, h8750, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h6253, h8081, h8741, hc01, hc12, hlam, hphi, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h7338, h8741, h8744, hc01, hc12, hlam, hphi, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h8736, hlam, p8777_0]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h8738, hlam, p8777_0]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [hlam, p8777_0]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h7338, h8081, h8741, h8744, hc01, hc12, hlam, hphi, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h8081, h8741, h8744, h8746, hc01, hc12, hlam, hphi, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h8737, hlam, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h8739, hlam, p8777_0]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [h8740, hlam, p8777_1]
                          · have p8777_0 := h8777c.1
                            have p8777_1 := h8777c.2.1
                            have p8777_2 := h8777c.2.2.1
                            have p8777_3 := h8777c.2.2.2
                            linarith only [hlam, p8777_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8803 | h8803
                        · linarith only [h0, h8735, h8747, h8749, h8803, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c | h8805c
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [hlam, p8805_0]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h0, hlam, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h6253, hlam, p8805_0]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h7338, hlam, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h8081, hlam, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [hlam, p8805_0]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h6253, h8741, hc01, hc12, hlam, hphi, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h8735, hlam, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [hlam, p8805_0]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h6253, h7338, h8741, hc01, hc12, hlam, hphi, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h6253, h8081, h8741, hc01, hc12, hlam, hphi, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h7338, h8741, h8744, hc01, hc12, hlam, hphi, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h8736, hlam, p8805_0]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h8738, hlam, p8805_0]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [hlam, p8805_0]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h7338, h8081, h8741, h8744, hc01, hc12, hlam, hphi, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h8081, h8741, h8744, h8746, hc01, hc12, hlam, hphi, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h8737, hlam, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h8739, hlam, p8805_0]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [h8740, hlam, p8805_1]
                          · have p8805_0 := h8805c.1
                            have p8805_1 := h8805c.2.1
                            have p8805_2 := h8805c.2.2.1
                            have p8805_3 := h8805c.2.2.2
                            linarith only [hlam, p8805_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8831 | h8831
                      · linarith only [h8747, h8748, h8831, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8833 | h8833
                        · linarith only [h6253, h8739, h8741, h8747, h8748, h8831, h8833, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c | h8835c
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [hlam, p8835_0]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h0, hlam, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h6253, hlam, p8835_0]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h7338, hlam, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h8081, hlam, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [hlam, p8835_0]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h0, h8740, h8748, h8833, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h6253, h8741, hc01, hc12, hlam, hphi, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h8735, hlam, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [hlam, p8835_0]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h6253, h8740, h8741, h8748, h8833, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h6253, h8081, h8741, hc01, hc12, hlam, hphi, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h7338, h8741, h8744, hc01, hc12, hlam, hphi, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h8736, hlam, p8835_0]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h8738, hlam, p8835_0]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [hlam, p8835_0]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h7338, h8739, h8741, h8744, h8748, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h8081, h8741, h8744, h8746, hc01, hc12, hlam, hphi, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h8737, hlam, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h8739, hlam, p8835_0]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [h8740, hlam, p8835_1]
                          · have p8835_0 := h8835c.1
                            have p8835_1 := h8835c.2.1
                            have p8835_2 := h8835c.2.2.1
                            have p8835_3 := h8835c.2.2.2
                            linarith only [hlam, p8835_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8861 | h8861
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8862 | h8862
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8863 | h8863
                        · rcases h0bigk with h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c | h8864c
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [hlam, p8864_0]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h0, hlam, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h6253, hlam, p8864_0]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h7338, hlam, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h8081, hlam, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [hlam, p8864_0]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h6253, h8741, hc01, hc12, hlam, hphi, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h8735, hlam, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [hlam, p8864_0]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h6253, h8736, h8741, h8747, h8861, h8863, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h6253, h8081, h8741, hc01, hc12, hlam, hphi, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h7338, h8741, h8744, hc01, hc12, hlam, hphi, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h8736, hlam, p8864_0]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h8738, hlam, p8864_0]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [hlam, p8864_0]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h7338, h8081, h8741, h8744, hc01, hc12, hlam, hphi, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h8081, h8741, h8744, h8746, hc01, hc12, hlam, hphi, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h8737, hlam, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h8739, hlam, p8864_0]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [h8740, hlam, p8864_1]
                          · have p8864_0 := h8864c.1
                            have p8864_1 := h8864c.2.1
                            have p8864_2 := h8864c.2.2.1
                            have p8864_3 := h8864c.2.2.2
                            linarith only [hlam, p8864_0]
                        · linarith only [h7338, h8740, h8741, h8744, h8747, h8861, h8863, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h8747, h8861, h8862, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8892 | h8892
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8893 | h8893
                        · rcases h0bigk with h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c | h8894c
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [hlam, p8894_0]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h0, hlam, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h6253, hlam, p8894_0]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h7338, hlam, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h8081, hlam, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [hlam, p8894_0]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h0, h8738, h8861, h8893, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h6253, h8741, hc01, hc12, hlam, hphi, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h8735, hlam, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [hlam, p8894_0]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h6253, h8736, h8741, h8892, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h6253, h8081, h8741, hc01, hc12, hlam, hphi, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h7338, h8741, h8744, hc01, hc12, hlam, hphi, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h8736, hlam, p8894_0]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h8738, hlam, p8894_0]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [hlam, p8894_0]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h7338, h8739, h8741, h8744, h8861, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h8081, h8741, h8744, h8746, hc01, hc12, hlam, hphi, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h8737, hlam, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h8739, hlam, p8894_0]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [h8740, hlam, p8894_1]
                          · have p8894_0 := h8894c.1
                            have p8894_1 := h8894c.2.1
                            have p8894_2 := h8894c.2.2.1
                            have p8894_3 := h8894c.2.2.2
                            linarith only [hlam, p8894_0]
                        · linarith only [h0, h8736, h8747, h8892, h8893, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8921 | h8921
                        · rcases h0bigk with h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c | h8922c
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [hlam, p8922_0]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h0, hlam, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h6253, hlam, p8922_0]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h7338, hlam, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h8081, hlam, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [hlam, p8922_0]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h0, h8738, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h6253, h8741, hc01, hc12, hlam, hphi, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h8735, hlam, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [hlam, p8922_0]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h6253, h7338, h8741, hc01, hc12, hlam, hphi, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h6253, h8081, h8741, hc01, hc12, hlam, hphi, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h7338, h8741, h8744, hc01, hc12, hlam, hphi, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h8736, hlam, p8922_0]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h8738, hlam, p8922_0]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [hlam, p8922_0]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h7338, h8739, h8741, h8744, h8747, h8892, h8921, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h8081, h8741, h8744, h8746, hc01, hc12, hlam, hphi, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h8737, hlam, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h8739, hlam, p8922_0]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [h8740, hlam, p8922_1]
                          · have p8922_0 := h8922c.1
                            have p8922_1 := h8922c.2.1
                            have p8922_2 := h8922c.2.2.1
                            have p8922_3 := h8922c.2.2.2
                            linarith only [hlam, p8922_0]
                        · rcases h0bigk with h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c | h8948c
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [hlam, p8948_0]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h0, hlam, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h6253, hlam, p8948_0]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h7338, hlam, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h8081, hlam, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [hlam, p8948_0]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h6253, h8741, hc01, hc12, hlam, hphi, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h8735, hlam, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [hlam, p8948_0]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h6253, h7338, h8741, hc01, hc12, hlam, hphi, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h6253, h8081, h8741, hc01, hc12, hlam, hphi, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h7338, h8741, h8744, hc01, hc12, hlam, hphi, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h8736, hlam, p8948_0]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h8738, hlam, p8948_0]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [hlam, p8948_0]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h7338, h8081, h8741, h8744, hc01, hc12, hlam, hphi, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h8081, h8741, h8744, h8746, hc01, hc12, hlam, hphi, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h8737, hlam, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h8739, hlam, p8948_0]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [h8740, hlam, p8948_1]
                          · have p8948_0 := h8948c.1
                            have p8948_1 := h8948c.2.1
                            have p8948_2 := h8948c.2.2.1
                            have p8948_3 := h8948c.2.2.2
                            linarith only [hlam, p8948_0]
                · linarith only [h7338, h8740, h8746, hlam]
              · linarith only [h6253, h8739, h8745, hlam]
            · linarith only [h6253, h8738, h8744, hlam]
          · linarith only [h0, h8737, h8743, hlam]
        · linarith only [h0, h8736, h8742, hlam]
      · linarith only [h0, h8735, h8741, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8980 | h8980
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8981 | h8981
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8982 | h8982
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8983 | h8983
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8984 | h8984
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8985 | h8985
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8986 | h8986
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8987 | h8987
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8988 | h8988
                      · linarith only [h8736, h8740, h8988, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8990 | h8990
                        · linarith only [h6253, h7338, h8735, h8740, h8980, h8986, h8990, hc01, hc12, hlam, hphi]
                        · rcases h0bigk with h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c | h8992c
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [hlam, p8992_0]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h0, hlam, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h6253, hlam, p8992_0]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h7338, hlam, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h8081, hlam, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [hlam, p8992_0]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h0, h7338, h8740, hc01, hc12, hlam, hphi, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h6253, h8980, hc01, hc12, hlam, hphi, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h8735, hlam, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [hlam, p8992_0]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h6253, h7338, h8980, hc01, hc12, hlam, hphi, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h6253, h7338, h8740, h8980, hc01, hc12, hlam, hphi, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h7338, h8980, h8983, hc01, hc12, hlam, hphi, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h8736, hlam, p8992_0]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h8738, hlam, p8992_0]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [hlam, p8992_0]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h8740, hlam, p8992_0]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h8081, hc01, hc15, hlam, hphi, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h8737, hlam, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h8739, hlam, p8992_0]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [h8740, h8980, h8983, h8985, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8992_1]
                          · have p8992_0 := h8992c.1
                            have p8992_1 := h8992c.2.1
                            have p8992_2 := h8992c.2.2.1
                            have p8992_3 := h8992c.2.2.2
                            linarith only [hlam, p8992_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9018 | h9018
                      · linarith only [h8736, h8740, h9018, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9020 | h9020
                        · linarith only [h8739, h8740, h8986, h8987, h9020, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c | h9022c
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [hlam, p9022_0]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h0, hlam, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h6253, hlam, p9022_0]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h7338, hlam, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h8081, hlam, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [hlam, p9022_0]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h0, h8739, h8987, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h6253, h8980, hc01, hc12, hlam, hphi, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h8735, hlam, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [hlam, p9022_0]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h6253, h7338, h8980, hc01, hc12, hlam, hphi, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h6253, h8739, h8980, h8986, h8987, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h7338, h8980, h8983, hc01, hc12, hlam, hphi, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h8736, hlam, p9022_0]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h8738, hlam, p9022_0]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [hlam, p9022_0]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h8740, hlam, p9022_0]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h8081, h8980, h8983, h8985, hc01, hc12, hlam, hphi, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h8737, hlam, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h8739, hlam, p9022_0]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [h8740, h8980, h8983, h8985, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9022_1]
                          · have p9022_0 := h9022c.1
                            have p9022_1 := h9022c.2.1
                            have p9022_2 := h9022c.2.2.1
                            have p9022_3 := h9022c.2.2.2
                            linarith only [hlam, p9022_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9048 | h9048
                    · linarith only [h8738, h8740, h8980, h8983, h8985, h8986, h9048, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9050 | h9050
                      · linarith only [h0, h8736, h8738, h8740, h8986, h9050, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9052 | h9052
                        · linarith only [h8738, h8740, h9052, hlam]
                        · rcases h0bigk with h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c | h9054c
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [hlam, p9054_0]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h0, hlam, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h6253, hlam, p9054_0]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h7338, hlam, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h8081, hlam, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [hlam, p9054_0]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h0, h8738, h8986, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h6253, h8980, hc01, hc12, hlam, hphi, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h8735, hlam, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [hlam, p9054_0]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h6253, h8738, h8980, h8986, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h6253, h8081, h8980, hc01, hc12, hlam, hphi, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h8740, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h8736, hlam, p9054_0]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h8738, hlam, p9054_0]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [hlam, p9054_0]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h8740, hlam, p9054_0]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h8081, h8980, h8983, h8985, hc01, hc12, hlam, hphi, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h8737, hlam, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h8739, hlam, p9054_0]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [h7338, h8081, h8980, h8983, h8985, hc01, hc12, hlam, hphi, p9054_1]
                          · have p9054_0 := h9054c.1
                            have p9054_1 := h9054c.2.1
                            have p9054_2 := h9054c.2.2.1
                            have p9054_3 := h9054c.2.2.2
                            linarith only [hlam, p9054_0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9080 | h9080
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9081 | h9081
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9082 | h9082
                      · linarith only [h7338, h8985, h9082, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9084 | h9084
                        · linarith only [h0, h7338, h8735, h8985, h9080, h9084, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c | h9086c
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [hlam, p9086_0]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h0, hlam, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h6253, hlam, p9086_0]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h7338, hlam, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h8081, hlam, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [hlam, p9086_0]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h6253, h8980, hc01, hc12, hlam, hphi, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h8735, hlam, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [hlam, p9086_0]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h6253, h7338, h8980, hc01, hc12, hlam, hphi, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h6253, h8081, h8980, hc01, hc12, hlam, hphi, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h7338, hc01, hc14, hlam, hphi, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h8736, hlam, p9086_0]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h8738, hlam, p9086_0]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [hlam, p9086_0]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h8740, hlam, p9086_0]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h8081, hc01, hc15, hlam, hphi, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h8737, hlam, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h8739, hlam, p9086_0]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [h8740, hc04, hc45, hlam, hphi, p9086_1]
                          · have p9086_0 := h9086c.1
                            have p9086_1 := h9086c.2.1
                            have p9086_2 := h9086c.2.2.1
                            have p9086_3 := h9086c.2.2.2
                            linarith only [hlam, p9086_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9112 | h9112
                      · linarith only [h7338, h8985, h9112, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9114 | h9114
                        · linarith only [h7338, h8985, h9114, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c | h9116c
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [hlam, p9116_0]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h0, hlam, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h6253, hlam, p9116_0]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h7338, hlam, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h8081, hlam, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [hlam, p9116_0]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h0, h8739, h9081, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h6253, h8980, hc01, hc12, hlam, hphi, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h8735, hlam, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [hlam, p9116_0]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h6253, h7338, h8980, hc01, hc12, hlam, hphi, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h6253, h8081, h8980, hc01, hc12, hlam, hphi, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h7338, hc01, hc14, hlam, hphi, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h8736, hlam, p9116_0]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h8738, hlam, p9116_0]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [hlam, p9116_0]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h8740, hlam, p9116_0]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h8081, hc01, hc15, hlam, hphi, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h8737, hlam, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h8739, hlam, p9116_0]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [h8740, hc04, hc45, hlam, hphi, p9116_1]
                          · have p9116_0 := h9116c.1
                            have p9116_1 := h9116c.2.1
                            have p9116_2 := h9116c.2.2.1
                            have p9116_3 := h9116c.2.2.2
                            linarith only [hlam, p9116_0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9142 | h9142
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9143 | h9143
                      · linarith only [h7338, h8738, h8985, h9080, h9142, h9143, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h9080, h9142, h9143, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9146 | h9146
                      · linarith only [h7338, h8985, h9146, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9148 | h9148
                        · linarith only [h7338, h8738, h8985, h9148, hlam]
                        · rcases h0bigk with h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c | h9150c
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [hlam, p9150_0]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h0, hlam, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h6253, hlam, p9150_0]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h7338, hlam, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h8081, hlam, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [hlam, p9150_0]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h0, h6253, hc01, hc12, hlam, hphi, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h6253, h8980, hc01, hc12, hlam, hphi, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h8735, hlam, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [hlam, p9150_0]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h6253, h7338, h8980, hc01, hc12, hlam, hphi, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h6253, h8081, h8980, hc01, hc12, hlam, hphi, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h7338, hc01, hc14, hlam, hphi, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h8736, hlam, p9150_0]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h8738, hlam, p9150_0]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [hlam, p9150_0]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h8740, hlam, p9150_0]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h8081, hc01, hc15, hlam, hphi, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h8737, hlam, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h8739, hlam, p9150_0]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [h8740, hc04, hc45, hlam, hphi, p9150_1]
                          · have p9150_0 := h9150c.1
                            have p9150_1 := h9150c.2.1
                            have p9150_2 := h9150c.2.2.1
                            have p9150_3 := h9150c.2.2.2
                            linarith only [hlam, p9150_0]
              · linarith only [h6253, h8739, h8984, hlam]
            · linarith only [h6253, h8738, h8983, hlam]
          · linarith only [h0, h8735, h8737, h8739, h8982, hlam]
        · linarith only [h0, h8736, h8981, hlam]
      · linarith only [h0, h8735, h8980, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9181 | h9181
    · linarith only [h8738, h8739, h9181, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9183 | h9183
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9184 | h9184
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9185 | h9185
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9186 | h9186
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9187 | h9187
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9188 | h9188
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9189 | h9189
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9190 | h9190
                    · linarith only [h0, h6253, h8735, h8739, h9190, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9192 | h9192
                      · linarith only [h8081, h8736, h8738, h8739, h9181, h9187, h9192, hc01, hc13, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9194 | h9194
                        · linarith only [h8735, h8739, h9181, h9183, h9187, h9189, h9194, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [hlam, p9196_0]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h0, hlam, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h6253, hlam, p9196_0]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h7338, hlam, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h8081, hlam, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [hlam, p9196_0]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h0, h8735, h9189, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h0, h8735, h8739, h9189, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h6253, h9183, hc01, hc12, hlam, hphi, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h8735, hlam, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [hlam, p9196_0]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h7338, h8081, h8739, h9183, h9186, h9188, hc01, hc12, hlam, hphi, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h8739, hlam, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h7338, h9183, h9186, hc01, hc12, hlam, hphi, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h8736, hlam, p9196_0]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h8738, hlam, p9196_0]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [hlam, p9196_0]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h9181, hlam, p9196_0]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h8081, h9183, h9186, h9188, hc01, hc12, hlam, hphi, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h8737, hlam, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h6253, h8081, h9183, h9186, h9188, hc01, hc12, hlam, hphi, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [h8739, h9183, h9186, h9188, h9194, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9196_1]
                          · have p9196_0 := h9196c.1
                            have p9196_1 := h9196c.2.1
                            have p9196_2 := h9196c.2.2.1
                            have p9196_3 := h9196c.2.2.2
                            linarith only [hlam, p9196_0]
                  · linarith only [h8738, h8739, h9183, h9187, h9189, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9223 | h9223
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9224 | h9224
                    · linarith only [h0, h6253, h8735, h8739, h9224, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9226 | h9226
                      · linarith only [h0, h8081, h8736, h9188, h9226, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9228 | h9228
                        · linarith only [h7338, h8735, h9188, h9223, h9228, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases h0bigk with h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c | h9230c
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [hlam, p9230_0]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h0, hlam, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h6253, hlam, p9230_0]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h7338, hlam, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h8081, hlam, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [hlam, p9230_0]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h0, h8735, h9223, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h0, h8081, hc01, hc12, hlam, hphi, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h6253, h9183, hc01, hc12, hlam, hphi, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h8735, hlam, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [hlam, p9230_0]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h6253, h7338, h9183, hc01, hc12, hlam, hphi, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h8739, hlam, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h7338, hc01, hc14, hlam, hphi, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h8736, hlam, p9230_0]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h8738, hlam, p9230_0]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [hlam, p9230_0]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h9181, hlam, p9230_0]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h8081, h9188, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h8737, hlam, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h8739, h9183, h9187, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [h7338, h8739, h9183, h9187, hc01, hc12, hlam, hphi, p9230_1]
                          · have p9230_0 := h9230c.1
                            have p9230_1 := h9230c.2.1
                            have p9230_2 := h9230c.2.2.1
                            have p9230_3 := h9230c.2.2.2
                            linarith only [hlam, p9230_0]
                  · linarith only [h8738, h8739, h9183, h9187, h9223, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9257 | h9257
                · linarith only [h7338, h9181, h9186, h9187, h9257, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9259 | h9259
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9260 | h9260
                    · linarith only [h6253, h9187, h9260, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9262 | h9262
                      · linarith only [h7338, h9257, h9262, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9264 | h9264
                        · linarith only [h6253, h7338, h8735, h9187, h9257, h9259, h9264, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [hlam, p9266_0]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h0, hlam, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h6253, hlam, p9266_0]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h7338, hlam, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h8081, hlam, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [hlam, p9266_0]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h0, h8735, h9259, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h0, h7338, hc01, hc12, hlam, hphi, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h0, h8735, h8739, h9259, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h6253, hc01, hc13, hlam, hphi, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h8735, hlam, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [hlam, p9266_0]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h6253, h7338, h9187, h9264, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h8739, hlam, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h7338, hc01, hc14, hlam, hphi, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h8736, hlam, p9266_0]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h8738, hlam, p9266_0]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [hlam, p9266_0]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h9181, hlam, p9266_0]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h8081, hc01, hc15, hlam, hphi, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h8737, hlam, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h8739, h9264, hc03, hc45, hlam, hphi, ht34, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [h7338, h8739, h9264, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9266_1]
                          · have p9266_0 := h9266c.1
                            have p9266_1 := h9266c.2.1
                            have p9266_2 := h9266c.2.2.1
                            have p9266_3 := h9266c.2.2.2
                            linarith only [hlam, p9266_0]
                  · linarith only [h6253, h8738, h9187, h9259, hc23, hc35, hlam, hphi]
            · linarith only [h6253, h8738, h9186, hlam]
          · linarith only [h0, h8737, h9185, hlam]
        · linarith only [h0, h8736, h9184, hlam]
      · linarith only [h0, h8735, h9183, hlam]

end R2N4
