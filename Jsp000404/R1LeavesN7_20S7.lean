import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5035 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5036 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5037 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h5038 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 1 2 3 (by decide) (by decide) with h5039 | h5039
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5040 | h5040
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5041 | h5041
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5042 | h5042
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5043 | h5043
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5044 | h5044
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5045 | h5045
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5046 | h5046
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5047 | h5047
                  · rcases h2bigk with h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c | h5048c
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h0, hlam, p5048_1]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5044, h5047, hc02, hc45, hlam, hphi, ht0b, ht5b, p5048_1]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h0, h5044, h5047, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5048_1]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      rcases p5048_3 (m.d 0 2) (by simp) with h5053 | h5053
                      · rcases p5048_3 (m.d 1 2) (by simp) with h5054 | h5054
                        · rcases p5048_3 (m.d 2 3) (by simp) with h5055 | h5055
                          · linarith only [h5034, h5055, hlam]
                          · linarith only [h5045, h5055, hlam]
                        · linarith only [h5041, h5054, hlam]
                      · linarith only [h5053, hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5048_1]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5044, h5047, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5048_1]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5044, h5047, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5048_1]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      rcases p5048_3 (m.d 0 2) (by simp) with h5064 | h5064
                      · linarith only [h0, h5064, hlam]
                      · linarith only [h5036, h5064, hlam]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5034, hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5039, hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5034, h5044, h5047, hc02, hc45, hlam, hphi, ht0b, ht5b, p5048_1]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h0, h5034, h5045, h5047, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5048_1]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5035, hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5040, hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5044, hlam, p5048_1]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h0, h5035, h5045, h5047, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5048_1]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5036, hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5041, hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5045, hlam, p5048_1]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [h5046, hlam, p5048_0]
                    · have p5048_0 := h5048c.1
                      have p5048_1 := h5048c.2.1
                      have p5048_2 := h5048c.2.2.1
                      have p5048_3 := h5048c.2.2.2
                      linarith only [hlam, p5048_0]
                  · rcases h2bigk with h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [hlam, p5082_0]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h0, hlam, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h0, h5044, h5046, h5047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h0, h5046, h5047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h0, h5046, h5047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [hlam, p5082_0]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5044, h5046, h5047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5046, h5047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5046, h5047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5034, hlam, p5082_0]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5039, hlam, p5082_0]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [hlam, p5082_0]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5034, h5046, h5047, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h0, h5034, h5046, h5047, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5035, hlam, p5082_0]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5040, hlam, p5082_0]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5044, hlam, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [hlam, p5082_0]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5035, h5046, h5047, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5036, hlam, p5082_0]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5041, hlam, p5082_0]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5045, hlam, p5082_1]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [h5046, hlam, p5082_0]
                    · have p5082_0 := h5082c.1
                      have p5082_1 := h5082c.2.1
                      have p5082_2 := h5082c.2.2.1
                      have p5082_3 := h5082c.2.2.2
                      linarith only [hlam, p5082_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5108 | h5108
                  · linarith only [h0, h5034, h5044, h5046, h5108, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases h2bigk with h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h0, hlam, p5110_1]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h0, h5044, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5110_1]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      rcases p5110_3 (m.d 0 2) (by simp) with h5114 | h5114
                      · rcases p5110_3 (m.d 1 2) (by simp) with h5115 | h5115
                        · rcases p5110_3 (m.d 2 3) (by simp) with h5116 | h5116
                          · linarith only [h5034, h5116, hlam]
                          · linarith only [h5044, h5116, hlam]
                        · linarith only [h5040, h5115, hlam]
                      · linarith only [h5114, hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      rcases p5110_3 (m.d 0 2) (by simp) with h5121 | h5121
                      · rcases p5110_3 (m.d 1 2) (by simp) with h5122 | h5122
                        · rcases p5110_3 (m.d 2 3) (by simp) with h5123 | h5123
                          · linarith only [h5034, h5123, hlam]
                          · linarith only [h5045, h5123, hlam]
                        · linarith only [h5041, h5122, hlam]
                      · linarith only [h5121, hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5110_1]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h5045, h5108, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5110_1]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      rcases p5110_3 (m.d 0 2) (by simp) with h5131 | h5131
                      · linarith only [h0, h5131, hlam]
                      · linarith only [h5035, h5131, hlam]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      rcases p5110_3 (m.d 0 2) (by simp) with h5134 | h5134
                      · linarith only [h0, h5134, hlam]
                      · linarith only [h5036, h5134, hlam]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h5034, hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h5039, hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h5034, h5044, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5110_1]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h0, h5034, h5044, h5046, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5110_1]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h5035, hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h5040, hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h5044, hlam, p5110_1]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h5046, hlam, p5110_1]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h5036, hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h5041, hlam, p5110_0]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h5045, hlam, p5110_1]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [h0, h5036, h5044, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5110_1]
                    · have p5110_0 := h5110c.1
                      have p5110_1 := h5110c.2.1
                      have p5110_2 := h5110c.2.2.1
                      have p5110_3 := h5110c.2.2.2
                      linarith only [hlam, p5110_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5152 | h5152
                · linarith only [h5044, h5045, h5152, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5154 | h5154
                  · linarith only [h0, h5034, h5044, h5152, h5154, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases h2bigk with h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h0, hlam, p5156_1]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h0, h5044, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5156_1]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      rcases p5156_3 (m.d 0 2) (by simp) with h5160 | h5160
                      · rcases p5156_3 (m.d 1 2) (by simp) with h5161 | h5161
                        · rcases p5156_3 (m.d 2 3) (by simp) with h5162 | h5162
                          · linarith only [h5034, h5162, hlam]
                          · linarith only [h5044, h5162, hlam]
                        · linarith only [h5040, h5161, hlam]
                      · linarith only [h5160, hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h0, h5044, h5045, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5156_1]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5034, h5037, h5038, h5154, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5156_1]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5044, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5156_1]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      rcases p5156_3 (m.d 0 2) (by simp) with h5171 | h5171
                      · linarith only [h0, h5171, hlam]
                      · linarith only [h5035, h5171, hlam]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5044, h5045, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5156_1]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5034, hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5039, hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5034, h5037, h5038, h5044, h5045, h5154, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5156_1]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5045, hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5035, hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5040, hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5044, hlam, p5156_1]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5152, hlam, p5156_1]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5036, hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h5041, hlam, p5156_0]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h0, h5036, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5156_1]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [h0, h5034, h5037, h5038, h5044, h5045, h5154, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5156_1]
                    · have p5156_0 := h5156c.1
                      have p5156_1 := h5156c.2.1
                      have p5156_2 := h5156c.2.2.1
                      have p5156_3 := h5156c.2.2.2
                      linarith only [hlam, p5156_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5190 | h5190
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5191 | h5191
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5192 | h5192
                  · rcases h2bigk with h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c | h5193c
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h0, hlam, p5193_1]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h0, h5190, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5193_1]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h0, h5044, h5190, h5192, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5193_1]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      rcases p5193_3 (m.d 0 2) (by simp) with h5198 | h5198
                      · rcases p5193_3 (m.d 1 2) (by simp) with h5199 | h5199
                        · rcases p5193_3 (m.d 2 3) (by simp) with h5200 | h5200
                          · linarith only [h5034, h5200, hlam]
                          · linarith only [h5190, h5200, hlam]
                        · linarith only [h5041, h5199, hlam]
                      · linarith only [h5198, hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5034, h5037, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5193_1]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5190, h5192, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5193_1]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5044, h5190, h5192, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5193_1]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      rcases p5193_3 (m.d 0 2) (by simp) with h5209 | h5209
                      · linarith only [h0, h5209, hlam]
                      · linarith only [h5036, h5209, hlam]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5034, hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5039, hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5044, hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5034, h5037, h5044, h5190, h5192, hc02, hc45, hlam, hphi, ht0b, ht5b, p5193_1]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5035, hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5040, hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h0, h5035, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5193_1]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h0, h5034, h5037, h5044, h5190, h5192, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5193_1]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5036, hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5041, hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5190, hlam, p5193_1]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [h5191, hlam, p5193_0]
                    · have p5193_0 := h5193c.1
                      have p5193_1 := h5193c.2.1
                      have p5193_2 := h5193c.2.2.1
                      have p5193_3 := h5193c.2.2.2
                      linarith only [hlam, p5193_0]
                  · linarith only [h5038, h5044, h5190, h5192, hc04, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h5044, h5190, h5191, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5229 | h5229
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5230 | h5230
                  · rcases h2bigk with h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c | h5231c
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h0, hlam, p5231_1]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      rcases p5231_3 (m.d 0 2) (by simp) with h5234 | h5234
                      · rcases p5231_3 (m.d 1 2) (by simp) with h5235 | h5235
                        · rcases p5231_3 (m.d 2 3) (by simp) with h5236 | h5236
                          · linarith only [h5236, hlam, p5231_0]
                          · rcases p5231_3 (m.d 2 4) (by simp) with h5238 | h5238
                            · linarith only [h5035, h5238, hlam]
                            · linarith only [h5044, h5238, hlam]
                        · linarith only [h5039, h5235, hlam]
                      · linarith only [h5234, hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h0, h5229, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5231_1]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      rcases p5231_3 (m.d 0 2) (by simp) with h5244 | h5244
                      · rcases p5231_3 (m.d 1 2) (by simp) with h5245 | h5245
                        · rcases p5231_3 (m.d 2 3) (by simp) with h5246 | h5246
                          · linarith only [h5034, h5246, hlam]
                          · rcases p5231_3 (m.d 2 4) (by simp) with h5248 | h5248
                            · linarith only [h5035, h5248, hlam]
                            · linarith only [h5229, h5248, hlam]
                        · linarith only [h5041, h5245, hlam]
                      · linarith only [h5244, hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5034, h5037, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5231_1]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      rcases p5231_3 (m.d 0 2) (by simp) with h5255 | h5255
                      · linarith only [h0, h5255, hlam]
                      · linarith only [h5034, h5255, hlam]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5229, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5231_1]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      rcases p5231_3 (m.d 0 2) (by simp) with h5259 | h5259
                      · linarith only [h0, h5259, hlam]
                      · linarith only [h5036, h5259, hlam]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5034, hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5039, hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5044, hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5190, hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5035, hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5040, hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5231_1]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5037, h5044, h5190, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5231_1]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5036, hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5041, hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h0, h5036, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5231_1]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [h5229, hlam, p5231_0]
                    · have p5231_0 := h5231c.1
                      have p5231_1 := h5231c.2.1
                      have p5231_2 := h5231c.2.2.1
                      have p5231_3 := h5231c.2.2.2
                      linarith only [hlam, p5231_0]
                  · linarith only [h5044, h5229, h5230, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5278 | h5278
                  · rcases h2bigk with h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c | h5279c
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h0, hlam, p5279_1]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      rcases p5279_3 (m.d 0 2) (by simp) with h5282 | h5282
                      · rcases p5279_3 (m.d 1 2) (by simp) with h5283 | h5283
                        · rcases p5279_3 (m.d 2 3) (by simp) with h5284 | h5284
                          · linarith only [h5284, hlam, p5279_0]
                          · rcases p5279_3 (m.d 2 4) (by simp) with h5286 | h5286
                            · linarith only [h5035, h5286, hlam]
                            · linarith only [h5044, h5286, hlam]
                        · linarith only [h5039, h5283, hlam]
                      · linarith only [h5282, hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      rcases p5279_3 (m.d 0 2) (by simp) with h5291 | h5291
                      · rcases p5279_3 (m.d 1 2) (by simp) with h5292 | h5292
                        · rcases p5279_3 (m.d 2 3) (by simp) with h5293 | h5293
                          · linarith only [h5034, h5293, hlam]
                          · rcases p5279_3 (m.d 2 4) (by simp) with h5295 | h5295
                            · linarith only [h5295, hlam, p5279_0]
                            · rcases p5279_3 (m.d 2 5) (by simp) with h5297 | h5297
                              · linarith only [h5036, h5297, hlam]
                              · linarith only [h5229, h5297, hlam]
                        · linarith only [h5040, h5292, hlam]
                      · linarith only [h5291, hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      rcases p5279_3 (m.d 0 2) (by simp) with h5302 | h5302
                      · rcases p5279_3 (m.d 1 2) (by simp) with h5303 | h5303
                        · rcases p5279_3 (m.d 2 3) (by simp) with h5304 | h5304
                          · linarith only [h5034, h5304, hlam]
                          · rcases p5279_3 (m.d 2 4) (by simp) with h5306 | h5306
                            · linarith only [h5035, h5306, hlam]
                            · rcases p5279_3 (m.d 2 5) (by simp) with h5308 | h5308
                              · linarith only [h5308, hlam, p5279_0]
                              · rcases h4bigk with h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c | h5310c
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [hlam, p5310_0]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h3667, hlam, p5310_0]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  rcases p5310_3 (m.d 0 4) (by simp) with h5313 | h5313
                                  · rcases p5310_3 (m.d 1 4) (by simp) with h5314 | h5314
                                    · rcases p5310_3 (m.d 2 4) (by simp) with h5315 | h5315
                                      · linarith only [h5035, h5315, hlam]
                                      · rcases p5310_3 (m.d 3 4) (by simp) with h5317 | h5317
                                        · linarith only [h5037, h5317, hlam]
                                        · linarith only [h5044, h5317, hlam]
                                    · linarith only [h5040, h5314, hlam]
                                  · linarith only [h5035, h5313, hlam]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h3667, h5229, h5278, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5310_1]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  rcases p5310_3 (m.d 0 4) (by simp) with h5323 | h5323
                                  · rcases p5310_3 (m.d 1 4) (by simp) with h5324 | h5324
                                    · rcases p5310_3 (m.d 2 4) (by simp) with h5325 | h5325
                                      · linarith only [h5035, h5325, hlam]
                                      · rcases p5310_3 (m.d 3 4) (by simp) with h5327 | h5327
                                        · linarith only [h5037, h5327, hlam]
                                        · linarith only [h5278, h5327, hlam]
                                    · linarith only [h5043, h5324, hlam]
                                  · linarith only [h5323, hlam, p5310_0]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5037, h5039, h5042, h5044, h5229, h5278, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5310_1]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [hlam, p5310_0]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  rcases p5310_3 (m.d 0 4) (by simp) with h5334 | h5334
                                  · linarith only [h3667, h5334, hlam]
                                  · linarith only [h5035, h5334, hlam]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5044, h5229, h5278, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5310_1]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  rcases p5310_3 (m.d 0 4) (by simp) with h5338 | h5338
                                  · linarith only [h3667, h5338, hlam]
                                  · linarith only [h5038, h5338, hlam]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5035, hlam, p5310_1]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5040, hlam, p5310_1]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [hlam, p5310_0]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5044, hlam, p5310_1]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5229, hlam, p5310_0]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5037, hlam, p5310_1]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5042, hlam, p5310_0]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  rcases p5310_3 (m.d 0 4) (by simp) with h5348 | h5348
                                  · rcases p5310_3 (m.d 1 4) (by simp) with h5349 | h5349
                                    · rcases p5310_3 (m.d 2 4) (by simp) with h5350 | h5350
                                      · linarith only [h5044, h5350, hlam]
                                      · rcases p5310_3 (m.d 3 4) (by simp) with h5352 | h5352
                                        · rcases p5310_3 (m.d 4 5) (by simp) with h5353 | h5353
                                          · linarith only [h5278, h5353, hlam]
                                          · linarith only [h5229, h5353, hlam]
                                        · linarith only [h5044, h5352, hlam]
                                    · linarith only [h5040, h5349, hlam]
                                  · linarith only [h5035, h5348, hlam]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [hlam, p5310_0]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5034, h5037, h5044, h5229, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5310_1]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5038, hlam, p5310_0]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5043, hlam, p5310_0]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h0, h5034, h5037, h5044, h5278, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5310_1]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [h5278, hlam, p5310_0]
                                · have p5310_0 := h5310c.1
                                  have p5310_1 := h5310c.2.1
                                  have p5310_2 := h5310c.2.2.1
                                  have p5310_3 := h5310c.2.2.2
                                  linarith only [hlam, p5310_0]
                        · linarith only [h5041, h5303, hlam]
                      · linarith only [h5302, hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h5034, h5037, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5279_1]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      rcases p5279_3 (m.d 0 2) (by simp) with h5370 | h5370
                      · linarith only [h0, h5370, hlam]
                      · linarith only [h5034, h5370, hlam]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      rcases p5279_3 (m.d 0 2) (by simp) with h5373 | h5373
                      · linarith only [h0, h5373, hlam]
                      · linarith only [h5035, h5373, hlam]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      rcases p5279_3 (m.d 0 2) (by simp) with h5376 | h5376
                      · linarith only [h0, h5376, hlam]
                      · linarith only [h5036, h5376, hlam]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h5034, hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h5039, hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h5044, hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h5190, hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h5035, hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h5040, hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h0, h5035, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5279_1]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h5229, hlam, p5279_1]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h5036, hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h5041, hlam, p5279_0]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h0, h5036, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5279_1]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [h0, h5034, h5037, h5229, h5278, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5279_1]
                    · have p5279_0 := h5279c.1
                      have p5279_1 := h5279c.2.1
                      have p5279_2 := h5279c.2.2.1
                      have p5279_3 := h5279c.2.2.2
                      linarith only [hlam, p5279_0]
                  · rcases h2bigk with h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h0, hlam, p5394_1]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      rcases p5394_3 (m.d 0 2) (by simp) with h5397 | h5397
                      · rcases p5394_3 (m.d 1 2) (by simp) with h5398 | h5398
                        · rcases p5394_3 (m.d 2 3) (by simp) with h5399 | h5399
                          · linarith only [h5399, hlam, p5394_0]
                          · rcases p5394_3 (m.d 2 4) (by simp) with h5401 | h5401
                            · linarith only [h5035, h5401, hlam]
                            · linarith only [h5044, h5401, hlam]
                        · linarith only [h5039, h5398, hlam]
                      · linarith only [h5397, hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      rcases p5394_3 (m.d 0 2) (by simp) with h5406 | h5406
                      · rcases p5394_3 (m.d 1 2) (by simp) with h5407 | h5407
                        · rcases p5394_3 (m.d 2 3) (by simp) with h5408 | h5408
                          · linarith only [h5034, h5408, hlam]
                          · rcases p5394_3 (m.d 2 4) (by simp) with h5410 | h5410
                            · linarith only [h5410, hlam, p5394_0]
                            · rcases p5394_3 (m.d 2 5) (by simp) with h5412 | h5412
                              · linarith only [h5036, h5412, hlam]
                              · linarith only [h5229, h5412, hlam]
                        · linarith only [h5040, h5407, hlam]
                      · linarith only [h5406, hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      rcases p5394_3 (m.d 0 2) (by simp) with h5417 | h5417
                      · rcases p5394_3 (m.d 1 2) (by simp) with h5418 | h5418
                        · rcases p5394_3 (m.d 2 3) (by simp) with h5419 | h5419
                          · linarith only [h5034, h5419, hlam]
                          · rcases p5394_3 (m.d 2 4) (by simp) with h5421 | h5421
                            · linarith only [h5035, h5421, hlam]
                            · rcases p5394_3 (m.d 2 5) (by simp) with h5423 | h5423
                              · linarith only [h5423, hlam, p5394_0]
                              · rcases h4bigk with h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c | h5425c
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [hlam, p5425_0]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h3667, hlam, p5425_0]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  rcases p5425_3 (m.d 0 4) (by simp) with h5428 | h5428
                                  · rcases p5425_3 (m.d 1 4) (by simp) with h5429 | h5429
                                    · rcases p5425_3 (m.d 2 4) (by simp) with h5430 | h5430
                                      · linarith only [h5035, h5430, hlam]
                                      · rcases p5425_3 (m.d 3 4) (by simp) with h5432 | h5432
                                        · linarith only [h5037, h5432, hlam]
                                        · linarith only [h5044, h5432, hlam]
                                    · linarith only [h5040, h5429, hlam]
                                  · linarith only [h5035, h5428, hlam]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  rcases p5425_3 (m.d 0 4) (by simp) with h5437 | h5437
                                  · rcases p5425_3 (m.d 1 4) (by simp) with h5438 | h5438
                                    · rcases p5425_3 (m.d 2 4) (by simp) with h5439 | h5439
                                      · linarith only [h5035, h5439, hlam]
                                      · rcases p5425_3 (m.d 3 4) (by simp) with h5441 | h5441
                                        · linarith only [h5037, h5441, hlam]
                                        · rcases p5425_3 (m.d 4 5) (by simp) with h5443 | h5443
                                          · linarith only [h5038, h5443, hlam]
                                          · linarith only [h5278, h5443, hlam]
                                    · linarith only [h5042, h5438, hlam]
                                  · linarith only [h5037, h5437, hlam]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5044, h5278, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5425_1]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5038, h5039, h5042, h5044, h5278, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5425_1]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [hlam, p5425_0]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  rcases p5425_3 (m.d 0 4) (by simp) with h5451 | h5451
                                  · linarith only [h3667, h5451, hlam]
                                  · linarith only [h5035, h5451, hlam]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  rcases p5425_3 (m.d 0 4) (by simp) with h5454 | h5454
                                  · linarith only [h3667, h5454, hlam]
                                  · linarith only [h5037, h5454, hlam]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5044, h5278, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5425_1]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5035, hlam, p5425_1]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5040, hlam, p5425_1]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [hlam, p5425_0]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5044, hlam, p5425_1]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5229, hlam, p5425_0]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5037, hlam, p5425_1]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5042, hlam, p5425_0]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5038, h5278, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p5425_1]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [hlam, p5425_0]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5278, hlam, p5425_0]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5038, hlam, p5425_0]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h5043, hlam, p5425_0]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  rcases p5425_3 (m.d 0 4) (by simp) with h5470 | h5470
                                  · rcases p5425_3 (m.d 1 4) (by simp) with h5471 | h5471
                                    · rcases p5425_3 (m.d 2 4) (by simp) with h5472 | h5472
                                      · linarith only [h5472, hlam, p5425_0]
                                      · rcases p5425_3 (m.d 3 4) (by simp) with h5474 | h5474
                                        · linarith only [h5278, h5474, hlam]
                                        · linarith only [h5044, h5474, hlam]
                                    · linarith only [h5040, h5471, hlam]
                                  · linarith only [h5035, h5470, hlam]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [h3667, h5038, h5039, h5042, h5044, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5425_1]
                                · have p5425_0 := h5425c.1
                                  have p5425_1 := h5425c.2.1
                                  have p5425_2 := h5425c.2.2.1
                                  have p5425_3 := h5425c.2.2.2
                                  linarith only [hlam, p5425_0]
                        · linarith only [h5041, h5418, hlam]
                      · linarith only [h5417, hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p5394_1]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      rcases p5394_3 (m.d 0 2) (by simp) with h5485 | h5485
                      · linarith only [h0, h5485, hlam]
                      · linarith only [h5034, h5485, hlam]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      rcases p5394_3 (m.d 0 2) (by simp) with h5488 | h5488
                      · linarith only [h0, h5488, hlam]
                      · linarith only [h5035, h5488, hlam]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      rcases p5394_3 (m.d 0 2) (by simp) with h5491 | h5491
                      · linarith only [h0, h5491, hlam]
                      · linarith only [h5036, h5491, hlam]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h5034, hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h5039, hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h5044, hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h5190, hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h5035, hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h5040, hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5394_1]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h5229, hlam, p5394_1]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h5036, hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h5041, hlam, p5394_0]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h3667, h5038, h5039, h5042, h5190, h5278, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5394_1]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [h3667, h5038, h5039, h5042, h5190, h5278, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5394_1]
                    · have p5394_0 := h5394c.1
                      have p5394_1 := h5394c.2.1
                      have p5394_2 := h5394c.2.2.1
                      have p5394_3 := h5394c.2.2.2
                      linarith only [hlam, p5394_0]
          · linarith only [h3667, h5038, h5043, hlam]
        · linarith only [h3667, h5037, h5042, hlam]
      · linarith only [h0, h5035, h5036, h5038, h5041, hlam]
    · linarith only [h0, h5035, h5040, hlam]
  · linarith only [h0, h5034, h5039, hlam]

end R2N4
