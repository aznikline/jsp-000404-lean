import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7862000 in
set_option maxHeartbeats 7862000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s7_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg4610 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6681 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8056 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h10831 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h11080 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h4610 := hg4610
  have h6681 := hg6681
  have h7494 := hg7494
  rcases m.htr 0 3 5 (by decide) (by decide) with h11081 | h11081
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11082 | h11082
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11083 | h11083
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11084 | h11084
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11085 | h11085
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11086 | h11086
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11087 | h11087
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11088 | h11088
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11089 | h11089
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11090 | h11090
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11091 | h11091
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11092 | h11092
                        · rcases h0bigk with h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c | h11093c
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [hlam, p11093_0]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h0, hlam, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h4610, hlam, p11093_0]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h6681, hlam, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h7494, hlam, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h10831, h11085, h11088, hc01, hc14, hlam, hphi, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [hlam, p11093_0]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h8056, hlam, p11093_0]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h10364, hlam, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h10831, hlam, p11093_0]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h11083, h8056, hc01, hc12, hlam, hphi, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h0, h11083, h8056, hc01, hc12, hlam, hphi, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [hlam, p11093_0]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h11083, h6681, h8056, hc01, hc12, hlam, hphi, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h0, h10831, h11083, h8056, hc01, hc12, hlam, hphi, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h11080, h11083, h8056, hc01, hc12, hlam, hphi, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h0, h11080, h11083, h8056, hc01, hc12, hlam, hphi, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h11080, hlam, p11093_0]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [hlam, p11093_0]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h0, h10831, h11080, h11083, h8056, hc01, hc12, hlam, hphi, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h11081, h11083, h8056, hc01, hc12, hlam, hphi, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h0, h11081, h11083, h8056, hc01, hc12, hlam, hphi, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h11081, hlam, p11093_0]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [h11082, hlam, p11093_1]
                          · have p11093_0 := h11093c.1
                            have p11093_1 := h11093c.2.1
                            have p11093_2 := h11093c.2.2.1
                            have p11093_3 := h11093c.2.2.2
                            linarith only [hlam, p11093_0]
                        · rcases h0bigk with h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c | h11119c
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [hlam, p11119_0]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h0, hlam, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h4610, hlam, p11119_0]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h6681, hlam, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h7494, hlam, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h11083, h8056, hc01, hc12, hlam, hphi, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [hlam, p11119_0]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h8056, hlam, p11119_0]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h10364, hlam, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h10831, hlam, p11119_0]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h11083, h8056, hc01, hc12, hlam, hphi, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h0, h11083, h8056, hc01, hc12, hlam, hphi, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [hlam, p11119_0]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h11082, h11083, h11092, h8056, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h11083, h7494, h8056, hc01, hc12, hlam, hphi, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h10364, h11083, h11089, hc01, hc12, hlam, hphi, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h0, h10364, h11083, h11089, hc01, hc12, hlam, hphi, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h11080, hlam, p11119_0]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [hlam, p11119_0]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h0, h10364, h10831, h11083, h11089, hc01, hc12, hlam, hphi, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h10831, h11083, h11089, h11091, hc01, hc12, hlam, hphi, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h0, h10831, h11083, h11089, h11091, hc01, hc12, hlam, hphi, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h11081, hlam, p11119_0]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [h11082, hlam, p11119_1]
                          · have p11119_0 := h11119c.1
                            have p11119_1 := h11119c.2.1
                            have p11119_2 := h11119c.2.2.1
                            have p11119_3 := h11119c.2.2.2
                            linarith only [hlam, p11119_0]
                      · linarith only [h10364, h11082, h11091, hlam]
                    · linarith only [h11081, h11090, h8056, hlam]
                  · linarith only [h11080, h11089, h8056, hlam]
                · linarith only [h11082, h11088, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h11081, h11083, h11087, h4610, h8056, hc01, hc12, hlam, hphi]
            · linarith only [h11080, h11083, h11086, h8056, hlam]
          · linarith only [h0, h11083, h11085, h8056, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11083, h11084, h8056, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11153 | h11153
        · linarith only [h0, h10364, h11083, h11153, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11155 | h11155
          · linarith only [h0, h10831, h11083, h11155, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11157 | h11157
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11158 | h11158
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11159 | h11159
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11160 | h11160
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11161 | h11161
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11162 | h11162
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11163 | h11163
                        · rcases h0bigk with h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [hlam, p11164_0]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h0, hlam, p11164_1]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h4610, hlam, p11164_0]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h6681, hlam, p11164_1]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h7494, hlam, p11164_1]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h0, h11155, h11160, h11162, hc01, hc23, hlam, hphi, ht12, p11164_1]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [hlam, p11164_0]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h8056, hlam, p11164_0]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h10364, hlam, p11164_1]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h10831, hlam, p11164_0]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            rcases p11164_3 (m.d 0 1) (by simp) with h11175 | h11175
                            · linarith only [h11175, h4610, hlam]
                            · rcases p11164_3 (m.d 0 2) (by simp) with h11177 | h11177
                              · linarith only [h11177, h8056, hlam]
                              · linarith only [h0, h11177, hlam]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            rcases p11164_3 (m.d 0 1) (by simp) with h11180 | h11180
                            · linarith only [h11180, h4610, hlam]
                            · rcases p11164_3 (m.d 0 2) (by simp) with h11182 | h11182
                              · linarith only [h11182, h8056, hlam]
                              · rcases p11164_3 (m.d 0 3) (by simp) with h11184 | h11184
                                · rcases p11164_3 (m.d 0 4) (by simp) with h11185 | h11185
                                  · linarith only [h11080, h11185, hlam]
                                  · linarith only [h10364, h11185, hlam]
                                · linarith only [h11184, h8056, hlam]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [hlam, p11164_0]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h11082, hc45, hlam, hphi, ht0b, ht5b, p11164_1, u0elo2]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            rcases p11164_3 (m.d 0 1) (by simp) with h11191 | h11191
                            · linarith only [h11191, h4610, hlam]
                            · rcases p11164_3 (m.d 0 2) (by simp) with h11193 | h11193
                              · linarith only [h11193, h8056, hlam]
                              · rcases p11164_3 (m.d 0 3) (by simp) with h11195 | h11195
                                · rcases p11164_3 (m.d 0 4) (by simp) with h11196 | h11196
                                  · linarith only [h11080, h11196, hlam]
                                  · linarith only [h11082, h11196, hlam]
                                · linarith only [h11081, h11195, hlam]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            rcases p11164_3 (m.d 0 1) (by simp) with h11200 | h11200
                            · linarith only [h11200, h6681, hlam]
                            · rcases p11164_3 (m.d 0 2) (by simp) with h11202 | h11202
                              · linarith only [h10364, h11202, hlam]
                              · linarith only [h0, h11202, hlam]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            rcases p11164_3 (m.d 0 1) (by simp) with h11205 | h11205
                            · linarith only [h11205, h6681, hlam]
                            · rcases p11164_3 (m.d 0 2) (by simp) with h11207 | h11207
                              · linarith only [h10364, h11207, hlam]
                              · rcases p11164_3 (m.d 0 3) (by simp) with h11209 | h11209
                                · rcases p11164_3 (m.d 0 4) (by simp) with h11210 | h11210
                                  · rcases p11164_3 (m.d 0 5) (by simp) with h11211 | h11211
                                    · linarith only [h11082, h11211, hlam]
                                    · linarith only [h10831, h11211, hlam]
                                  · linarith only [h10364, h11210, hlam]
                                · linarith only [h11209, h8056, hlam]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h11080, hlam, p11164_0]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [hlam, p11164_0]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            rcases p11164_3 (m.d 0 1) (by simp) with h11218 | h11218
                            · linarith only [h11218, h6681, hlam]
                            · rcases p11164_3 (m.d 0 2) (by simp) with h11220 | h11220
                              · linarith only [h10364, h11220, hlam]
                              · rcases p11164_3 (m.d 0 3) (by simp) with h11222 | h11222
                                · rcases p11164_3 (m.d 0 4) (by simp) with h11223 | h11223
                                  · rcases p11164_3 (m.d 0 5) (by simp) with h11224 | h11224
                                    · linarith only [h11082, h11224, hlam]
                                    · rcases h2bigk with h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c | h11226c
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [hlam, p11226_0]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h0, hlam, p11226_1]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h8056, hlam, p11226_0]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h10364, hlam, p11226_0]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h10831, hlam, p11226_0]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h0, h11155, h11160, h11162, hc01, hc23, hlam, hphi, ht12, p11226_1]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [hlam, p11226_0]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h11083, hlam, p11226_0]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h11153, hlam, p11226_0]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h11155, hlam, p11226_0]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        rcases p11226_3 (m.d 0 2) (by simp) with h11237 | h11237
                                        · linarith only [h11237, hlam, p11226_0]
                                        · rcases p11226_3 (m.d 1 2) (by simp) with h11239 | h11239
                                          · linarith only [h11083, h11239, hlam]
                                          · linarith only [h0, h11239, hlam]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p11226_1]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [hlam, p11226_0]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h0, h10364, hc01, hc23, hlam, hphi, ht12, p11226_1]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h0, h10831, hc01, hc23, hlam, hphi, ht12, p11226_1]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        rcases p11226_3 (m.d 0 2) (by simp) with h11246 | h11246
                                        · linarith only [h11246, hlam, p11226_0]
                                        · rcases p11226_3 (m.d 1 2) (by simp) with h11248 | h11248
                                          · linarith only [h11153, h11248, hlam]
                                          · linarith only [h0, h11248, hlam]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11226_1]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h11160, hlam, p11226_1]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [hlam, p11226_0]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h0, h11155, h11160, hc01, hc23, hlam, hphi, ht12, p11226_1]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        rcases p11226_3 (m.d 0 2) (by simp) with h11255 | h11255
                                        · linarith only [h11255, hlam, p11226_0]
                                        · rcases p11226_3 (m.d 1 2) (by simp) with h11257 | h11257
                                          · linarith only [h11155, h11257, hlam]
                                          · linarith only [h0, h11257, hlam]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11226_1]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h11161, hlam, p11226_1]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [h11162, hlam, p11226_0]
                                      · have p11226_0 := h11226c.1
                                        have p11226_1 := h11226c.2.1
                                        have p11226_2 := h11226c.2.2.1
                                        have p11226_3 := h11226c.2.2.2
                                        linarith only [hlam, p11226_0]
                                  · linarith only [h11082, h11223, hlam]
                                · linarith only [h11081, h11222, hlam]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            rcases p11164_3 (m.d 0 1) (by simp) with h11266 | h11266
                            · linarith only [h11266, h7494, hlam]
                            · rcases p11164_3 (m.d 0 2) (by simp) with h11268 | h11268
                              · linarith only [h10831, h11268, hlam]
                              · linarith only [h0, h11268, hlam]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            rcases p11164_3 (m.d 0 1) (by simp) with h11271 | h11271
                            · linarith only [h11271, h7494, hlam]
                            · rcases p11164_3 (m.d 0 2) (by simp) with h11273 | h11273
                              · linarith only [h10831, h11273, hlam]
                              · rcases p11164_3 (m.d 0 3) (by simp) with h11275 | h11275
                                · rcases p11164_3 (m.d 0 4) (by simp) with h11276 | h11276
                                  · rcases p11164_3 (m.d 0 5) (by simp) with h11277 | h11277
                                    · rcases h2bigk with h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c | h11278c
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [hlam, p11278_0]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h0, hlam, p11278_1]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h8056, hlam, p11278_0]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h10364, hlam, p11278_0]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h10831, hlam, p11278_0]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h0, h11083, hc01, hc23, hlam, hphi, ht12, p11278_1]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [hlam, p11278_0]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h11083, hlam, p11278_0]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h11153, hlam, p11278_0]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h11155, hlam, p11278_0]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        rcases p11278_3 (m.d 0 2) (by simp) with h11289 | h11289
                                        · linarith only [h11289, hlam, p11278_0]
                                        · rcases p11278_3 (m.d 1 2) (by simp) with h11291 | h11291
                                          · linarith only [h11083, h11291, hlam]
                                          · linarith only [h0, h11291, hlam]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p11278_1]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [hlam, p11278_0]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h0, h10364, hc01, hc23, hlam, hphi, ht12, p11278_1]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h0, h10831, hc01, hc23, hlam, hphi, ht12, p11278_1]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        rcases p11278_3 (m.d 0 2) (by simp) with h11298 | h11298
                                        · linarith only [h11298, hlam, p11278_0]
                                        · rcases p11278_3 (m.d 1 2) (by simp) with h11300 | h11300
                                          · linarith only [h11153, h11300, hlam]
                                          · linarith only [h0, h11300, hlam]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11278_1]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h11160, hlam, p11278_1]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [hlam, p11278_0]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h0, h11155, h11160, h7494, hc01, hc23, hlam, hphi, ht12, p11164_1, p11278_1]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        rcases p11278_3 (m.d 0 2) (by simp) with h11307 | h11307
                                        · linarith only [h11307, hlam, p11278_0]
                                        · rcases p11278_3 (m.d 1 2) (by simp) with h11309 | h11309
                                          · linarith only [h11155, h11309, hlam]
                                          · linarith only [h0, h11309, hlam]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11278_1]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h11161, hlam, p11278_1]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [h11162, hlam, p11278_0]
                                      · have p11278_0 := h11278c.1
                                        have p11278_1 := h11278c.2.1
                                        have p11278_2 := h11278c.2.2.1
                                        have p11278_3 := h11278c.2.2.2
                                        linarith only [hlam, p11278_0]
                                    · linarith only [h10831, h11277, hlam]
                                  · linarith only [h10364, h11276, hlam]
                                · linarith only [h11275, h8056, hlam]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h11081, hlam, p11164_0]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [h11082, hlam, p11164_1]
                          · have p11164_0 := h11164c.1
                            have p11164_1 := h11164c.2.1
                            have p11164_2 := h11164c.2.2.1
                            have p11164_3 := h11164c.2.2.2
                            linarith only [hlam, p11164_0]
                        · rcases h0bigk with h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c | h11322c
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [hlam, p11322_0]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h0, hlam, p11322_1]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h4610, hlam, p11322_0]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h6681, hlam, p11322_1]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h7494, hlam, p11322_1]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h8056, hc01, hc23, hlam, hphi, ht12, p11322_1]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [hlam, p11322_0]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h8056, hlam, p11322_0]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h10364, hlam, p11322_1]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h10831, hlam, p11322_0]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            rcases p11322_3 (m.d 0 1) (by simp) with h11333 | h11333
                            · linarith only [h11333, h4610, hlam]
                            · rcases p11322_3 (m.d 0 2) (by simp) with h11335 | h11335
                              · linarith only [h11335, h8056, hlam]
                              · linarith only [h0, h11335, hlam]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            rcases p11322_3 (m.d 0 1) (by simp) with h11338 | h11338
                            · linarith only [h11338, h4610, hlam]
                            · rcases p11322_3 (m.d 0 2) (by simp) with h11340 | h11340
                              · linarith only [h11340, h8056, hlam]
                              · rcases p11322_3 (m.d 0 3) (by simp) with h11342 | h11342
                                · rcases p11322_3 (m.d 0 4) (by simp) with h11343 | h11343
                                  · linarith only [h11080, h11343, hlam]
                                  · linarith only [h10364, h11343, hlam]
                                · linarith only [h11342, h8056, hlam]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [hlam, p11322_0]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h11082, h11163, hc34, hlam, hphi, ht0b, ht45, ht5b, p11322_1, u0elo2]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h11082, h11163, hc34, hlam, hphi, ht0b, ht45, ht5b, p11322_1, u0elo2]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            rcases p11322_3 (m.d 0 1) (by simp) with h11350 | h11350
                            · linarith only [h11350, h6681, hlam]
                            · rcases p11322_3 (m.d 0 2) (by simp) with h11352 | h11352
                              · linarith only [h10364, h11352, hlam]
                              · linarith only [h0, h11352, hlam]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            rcases p11322_3 (m.d 0 1) (by simp) with h11355 | h11355
                            · linarith only [h11355, h6681, hlam]
                            · rcases p11322_3 (m.d 0 2) (by simp) with h11357 | h11357
                              · linarith only [h10364, h11357, hlam]
                              · rcases p11322_3 (m.d 0 3) (by simp) with h11359 | h11359
                                · rcases p11322_3 (m.d 0 4) (by simp) with h11360 | h11360
                                  · rcases p11322_3 (m.d 0 5) (by simp) with h11361 | h11361
                                    · linarith only [h11082, h11361, hlam]
                                    · linarith only [h10831, h11361, hlam]
                                  · linarith only [h10364, h11360, hlam]
                                · linarith only [h11359, h8056, hlam]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h11080, hlam, p11322_0]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [hlam, p11322_0]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h11082, h11163, hc34, hlam, hphi, ht0b, ht45, ht5b, p11322_1, u0elo3]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            rcases p11322_3 (m.d 0 1) (by simp) with h11369 | h11369
                            · linarith only [h11369, h7494, hlam]
                            · rcases p11322_3 (m.d 0 2) (by simp) with h11371 | h11371
                              · linarith only [h10831, h11371, hlam]
                              · linarith only [h0, h11371, hlam]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            rcases p11322_3 (m.d 0 1) (by simp) with h11374 | h11374
                            · linarith only [h11374, h7494, hlam]
                            · rcases p11322_3 (m.d 0 2) (by simp) with h11376 | h11376
                              · linarith only [h10831, h11376, hlam]
                              · rcases p11322_3 (m.d 0 3) (by simp) with h11378 | h11378
                                · rcases p11322_3 (m.d 0 4) (by simp) with h11379 | h11379
                                  · rcases p11322_3 (m.d 0 5) (by simp) with h11380 | h11380
                                    · rcases h2bigk with h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c | h11381c
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [hlam, p11381_0]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h0, hlam, p11381_1]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h8056, hlam, p11381_0]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h10364, hlam, p11381_0]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h10831, hlam, p11381_0]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h0, h11155, h11160, h11162, hc01, hc23, hlam, hphi, ht12, p11381_1]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [hlam, p11381_0]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h11083, hlam, p11381_0]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h11153, hlam, p11381_0]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h11155, hlam, p11381_0]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        rcases p11381_3 (m.d 0 2) (by simp) with h11392 | h11392
                                        · linarith only [h11392, hlam, p11381_0]
                                        · rcases p11381_3 (m.d 1 2) (by simp) with h11394 | h11394
                                          · linarith only [h11083, h11394, hlam]
                                          · linarith only [h0, h11394, hlam]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p11381_1]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [hlam, p11381_0]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h0, h10364, hc01, hc23, hlam, hphi, ht12, p11381_1]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h0, h10831, hc01, hc23, hlam, hphi, ht12, p11381_1]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        rcases p11381_3 (m.d 0 2) (by simp) with h11401 | h11401
                                        · linarith only [h11401, hlam, p11381_0]
                                        · rcases p11381_3 (m.d 1 2) (by simp) with h11403 | h11403
                                          · linarith only [h11153, h11403, hlam]
                                          · linarith only [h0, h11403, hlam]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11381_1]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h11160, hlam, p11381_1]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [hlam, p11381_0]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h0, h11155, h11160, h7494, hc01, hc23, hlam, hphi, ht12, p11322_1, p11381_1]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        rcases p11381_3 (m.d 0 2) (by simp) with h11410 | h11410
                                        · linarith only [h11410, hlam, p11381_0]
                                        · rcases p11381_3 (m.d 1 2) (by simp) with h11412 | h11412
                                          · linarith only [h11155, h11412, hlam]
                                          · linarith only [h0, h11412, hlam]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11381_1]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h11161, hlam, p11381_1]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [h11162, hlam, p11381_0]
                                      · have p11381_0 := h11381c.1
                                        have p11381_1 := h11381c.2.1
                                        have p11381_2 := h11381c.2.2.1
                                        have p11381_3 := h11381c.2.2.2
                                        linarith only [hlam, p11381_0]
                                    · linarith only [h10831, h11380, hlam]
                                  · linarith only [h10364, h11379, hlam]
                                · linarith only [h11378, h8056, hlam]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h11081, hlam, p11322_0]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [h11082, hlam, p11322_1]
                          · have p11322_0 := h11322c.1
                            have p11322_1 := h11322c.2.1
                            have p11322_2 := h11322c.2.2.1
                            have p11322_3 := h11322c.2.2.2
                            linarith only [hlam, p11322_0]
                      · linarith only [h10364, h11082, h11162, hlam]
                    · linarith only [h11081, h11161, h8056, hlam]
                  · linarith only [h0, h11083, h11160, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11080, h11082, h11159, h6681, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h11081, h11158, h4610, hlam]
            · linarith only [h11080, h11157, h4610, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11431 | h11431
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11432 | h11432
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11433 | h11433
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11434 | h11434
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11435 | h11435
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11436 | h11436
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11437 | h11437
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11438 | h11438
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11439 | h11439
                      · linarith only [h0, h10364, h11082, h11431, h11437, h11439, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h10364, h11434, h11436, h11439, hc01, hc13, hlam, hphi]
                    · linarith only [h11081, h11438, h8056, hlam]
                  · linarith only [h11080, h11437, h8056, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11444 | h11444
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11445 | h11445
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11446 | h11446
                      · linarith only [h11436, h11446, h6681, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11448 | h11448
                        · linarith only [h0, h10364, h11080, h11432, h11436, h11448, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases h0bigk with h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c | h11450c
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [hlam, p11450_0]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h0, hlam, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h4610, hlam, p11450_0]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h6681, hlam, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h7494, hlam, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h10364, h11432, hc01, hc14, hlam, hphi, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [hlam, p11450_0]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h8056, hlam, p11450_0]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h10364, hlam, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h10831, hlam, p11450_0]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h11431, h8056, hc01, hc12, hlam, hphi, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h0, h11431, h8056, hc01, hc12, hlam, hphi, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [hlam, p11450_0]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h11431, h6681, h8056, hc01, hc12, hlam, hphi, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h11431, h7494, h8056, hc01, hc12, hlam, hphi, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h11436, h6681, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h0, h10364, h11432, h11436, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h11080, hlam, p11450_0]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [hlam, p11450_0]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h11082, hlam, p11450_0]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h11081, h11431, h8056, hc01, hc12, hlam, hphi, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h0, h11081, h11431, h8056, hc01, hc12, hlam, hphi, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h11081, hlam, p11450_0]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [h11081, h11431, h6681, h8056, hc01, hc12, hlam, hphi, p11450_1]
                          · have p11450_0 := h11450c.1
                            have p11450_1 := h11450c.2.1
                            have p11450_2 := h11450c.2.2.1
                            have p11450_3 := h11450c.2.2.2
                            linarith only [hlam, p11450_0]
                    · linarith only [h11081, h11445, h8056, hlam]
                  · linarith only [h0, h11080, h11436, h11444, h6681, h8056, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h11081, h11435, h4610, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h11080, h11431, h11434, h8056, hlam]
          · linarith only [h0, h11431, h11433, h8056, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11431, h11432, h8056, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11482 | h11482
        · linarith only [h0, h10364, h11431, h11482, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11484 | h11484
          · linarith only [h0, h10831, h11431, h11484, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11486 | h11486
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11487 | h11487
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11488 | h11488
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11489 | h11489
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11490 | h11490
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11491 | h11491
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11492 | h11492
                        · linarith only [h0, h10364, h11080, h11082, h11492, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases h0bigk with h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [hlam, p11494_0]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h0, hlam, p11494_1]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h4610, hlam, p11494_0]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h6681, hlam, p11494_1]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h7494, hlam, p11494_1]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h0, h11484, h11489, h11491, hc01, hc23, hlam, hphi, ht12, p11494_1]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [hlam, p11494_0]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h8056, hlam, p11494_0]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h10364, hlam, p11494_1]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h10831, hlam, p11494_0]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            rcases p11494_3 (m.d 0 1) (by simp) with h11505 | h11505
                            · linarith only [h11505, h4610, hlam]
                            · rcases p11494_3 (m.d 0 2) (by simp) with h11507 | h11507
                              · linarith only [h11507, h8056, hlam]
                              · linarith only [h0, h11507, hlam]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            rcases p11494_3 (m.d 0 1) (by simp) with h11510 | h11510
                            · linarith only [h11510, h4610, hlam]
                            · rcases p11494_3 (m.d 0 2) (by simp) with h11512 | h11512
                              · linarith only [h11512, h8056, hlam]
                              · rcases p11494_3 (m.d 0 3) (by simp) with h11514 | h11514
                                · rcases p11494_3 (m.d 0 4) (by simp) with h11515 | h11515
                                  · linarith only [h11080, h11515, hlam]
                                  · linarith only [h10364, h11515, hlam]
                                · linarith only [h11514, h8056, hlam]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [hlam, p11494_0]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            rcases p11494_3 (m.d 0 1) (by simp) with h11520 | h11520
                            · linarith only [h11520, h4610, hlam]
                            · rcases p11494_3 (m.d 0 2) (by simp) with h11522 | h11522
                              · linarith only [h11522, h8056, hlam]
                              · rcases p11494_3 (m.d 0 3) (by simp) with h11524 | h11524
                                · rcases p11494_3 (m.d 0 4) (by simp) with h11525 | h11525
                                  · linarith only [h11080, h11525, hlam]
                                  · rcases p11494_3 (m.d 0 5) (by simp) with h11527 | h11527
                                    · linarith only [h11081, h11527, hlam]
                                    · linarith only [h11082, h11527, hlam]
                                · linarith only [h11080, h11524, hlam]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            rcases p11494_3 (m.d 0 1) (by simp) with h11531 | h11531
                            · linarith only [h11531, h4610, hlam]
                            · rcases p11494_3 (m.d 0 2) (by simp) with h11533 | h11533
                              · linarith only [h11533, h8056, hlam]
                              · rcases p11494_3 (m.d 0 3) (by simp) with h11535 | h11535
                                · rcases p11494_3 (m.d 0 4) (by simp) with h11536 | h11536
                                  · linarith only [h11080, h11536, hlam]
                                  · rcases p11494_3 (m.d 0 5) (by simp) with h11538 | h11538
                                    · linarith only [h11081, h11538, hlam]
                                    · rcases h2bigk with h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c | h11540c
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [hlam, p11540_0]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h0, hlam, p11540_1]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h8056, hlam, p11540_0]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h10364, hlam, p11540_0]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h10831, hlam, p11540_0]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h0, h11484, h11489, h11491, hc01, hc23, hlam, hphi, ht12, p11540_1]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [hlam, p11540_0]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h11431, hlam, p11540_0]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h11482, hlam, p11540_0]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h11484, hlam, p11540_0]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        rcases p11540_3 (m.d 0 2) (by simp) with h11551 | h11551
                                        · linarith only [h11551, hlam, p11540_0]
                                        · rcases p11540_3 (m.d 1 2) (by simp) with h11553 | h11553
                                          · linarith only [h11431, h11553, hlam]
                                          · linarith only [h0, h11553, hlam]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p11540_1]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [hlam, p11540_0]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h0, h10364, hc01, hc23, hlam, hphi, ht12, p11540_1]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h0, h11484, hc01, hc23, hlam, hphi, ht12, p11540_1]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        rcases p11540_3 (m.d 0 2) (by simp) with h11560 | h11560
                                        · linarith only [h11560, hlam, p11540_0]
                                        · rcases p11540_3 (m.d 1 2) (by simp) with h11562 | h11562
                                          · linarith only [h11482, h11562, hlam]
                                          · linarith only [h0, h11562, hlam]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p11540_1]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h11489, hlam, p11540_1]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [hlam, p11540_0]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h0, h11484, h11489, hc01, hc23, hlam, hphi, ht12, p11540_1]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        rcases p11540_3 (m.d 0 2) (by simp) with h11569 | h11569
                                        · linarith only [h11569, hlam, p11540_0]
                                        · rcases p11540_3 (m.d 1 2) (by simp) with h11571 | h11571
                                          · linarith only [h11484, h11571, hlam]
                                          · linarith only [h0, h11571, hlam]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p11540_1]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h11490, hlam, p11540_1]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [h11491, hlam, p11540_0]
                                      · have p11540_0 := h11540c.1
                                        have p11540_1 := h11540c.2.1
                                        have p11540_2 := h11540c.2.2.1
                                        have p11540_3 := h11540c.2.2.2
                                        linarith only [hlam, p11540_0]
                                · linarith only [h11081, h11535, hlam]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h11082, h11488, hc01, hc15, hlam, hphi, p11494_1]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h0, h11082, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11494_1]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h11080, hlam, p11494_0]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [hlam, p11494_0]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h11082, hlam, p11494_0]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h11082, h11431, h11486, h11488, hc01, hc23, hlam, hphi, ht12, p11494_1]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h0, h11082, h11431, h11486, h11488, hc01, hc23, hlam, hphi, ht12, p11494_1]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h11081, hlam, p11494_0]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [h11082, h11431, h11486, h11488, h6681, hc01, hc23, hlam, hphi, ht12, p11494_1]
                          · have p11494_0 := h11494c.1
                            have p11494_1 := h11494c.2.1
                            have p11494_2 := h11494c.2.2.1
                            have p11494_3 := h11494c.2.2.2
                            linarith only [hlam, p11494_0]
                      · linarith only [h0, h10364, h11431, h11486, h11488, h11491, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h11081, h11082, h11431, h11486, h11488, h11490, hc05, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h11080, h11082, h11431, h11486, h11488, h11489, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11592 | h11592
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11593 | h11593
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11594 | h11594
                      · linarith only [h11488, h11594, h6681, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h11482, h11594, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h11081, h11431, h11593, h4610, hlam]
                  · linarith only [h0, h11080, h11431, h11592, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h11081, h11487, h4610, hlam]
            · linarith only [h11080, h11486, h4610, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11601 | h11601
    · linarith only [h11080, h11081, h11601, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11603 | h11603
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11604 | h11604
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11605 | h11605
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11606 | h11606
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11607 | h11607
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11608 | h11608
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11609 | h11609
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11610 | h11610
                    · linarith only [h11080, h11081, h11603, h11610, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h11607, h11610, h8056, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h11080, h11609, h8056, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11614 | h11614
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11615 | h11615
                    · linarith only [h11080, h11081, h11603, h11615, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h11603, h11607, h11615, h8056, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11080, h11081, h11603, h11607, h11614, h8056, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11619 | h11619
                · linarith only [h0, h10364, h11601, h11606, h11607, h11619, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11621 | h11621
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11622 | h11622
                    · linarith only [h11607, h11622, h4610, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11624 | h11624
                      · linarith only [h11604, h11619, h11624, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11626 | h11626
                        · linarith only [h0, h10364, h11080, h11604, h11619, h11626, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                        · rcases h0bigk with h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [hlam, p11628_0]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h0, hlam, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h4610, hlam, p11628_0]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h6681, hlam, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h7494, hlam, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h10364, h11604, hc01, hc14, hlam, hphi, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [hlam, p11628_0]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h8056, hlam, p11628_0]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h10364, hlam, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h10831, hlam, p11628_0]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h11603, h11607, h11626, h8056, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h11603, h11607, h11626, h8056, hc02, hc45, hlam, hphi, ht23, ht34, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [hlam, p11628_0]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h11603, h11607, h11626, h8056, hc04, hc45, hlam, hphi, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h11081, hlam, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h11080, h11603, h11607, h11626, h8056, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h0, h11080, h11603, h11607, h11626, h8056, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h11080, hlam, p11628_0]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [hlam, p11628_0]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h11601, hlam, p11628_0]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h10831, h11605, hc01, hc12, hlam, hphi, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h0, h10831, h11605, hc01, hc12, hlam, hphi, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h10831, h11080, h11605, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [h10831, h11605, h6681, hc01, hc12, hlam, hphi, p11628_1]
                          · have p11628_0 := h11628c.1
                            have p11628_1 := h11628c.2.1
                            have p11628_2 := h11628c.2.2.1
                            have p11628_3 := h11628c.2.2.2
                            linarith only [hlam, p11628_0]
                  · linarith only [h0, h11080, h11621, h8056, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h11080, h11603, h11606, h8056, hlam]
          · linarith only [h0, h11603, h11605, h8056, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11603, h11604, h8056, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h11658 | h11658
        · linarith only [h0, h10364, h11603, h11658, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11660 | h11660
          · linarith only [h0, h10831, h11603, h11660, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h11662 | h11662
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11663 | h11663
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11664 | h11664
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11665 | h11665
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11666 | h11666
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11667 | h11667
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11668 | h11668
                        · linarith only [h11080, h11081, h11601, h11603, h11663, h11668, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases h0bigk with h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [hlam, p11670_0]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h0, hlam, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h4610, hlam, p11670_0]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h6681, hlam, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h7494, hlam, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h8056, hc01, hc23, hlam, hphi, ht12, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [hlam, p11670_0]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h8056, hlam, p11670_0]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h10364, hlam, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h10831, hlam, p11670_0]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h11081, h11603, h11662, h11664, h11668, hc01, hc23, hlam, hphi, ht12, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h11081, h11603, h11662, h11664, h11668, hc02, hc23, hlam, hphi, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [hlam, p11670_0]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h0, h10364, h11081, h11603, h11662, h11664, h11668, hc01, hc23, hlam, hphi, ht12, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h11081, hlam, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h11080, h11081, h11603, h11662, h11664, h11668, hc01, hc23, hlam, hphi, ht12, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h0, h11080, h11081, h11603, h11662, h11664, h11668, hc01, hc23, hlam, hphi, ht12, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h11080, hlam, p11670_0]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [hlam, p11670_0]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h11601, hlam, p11670_0]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h11081, h11603, h11662, h11664, h11668, hc01, hc23, hlam, hphi, ht12, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h0, h11081, h11603, h11662, h11664, h11668, hc01, hc23, hlam, hphi, ht12, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h11080, h11081, h11603, h11662, h11664, h11668, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [h11081, h11603, h11662, h11664, h11668, h6681, hc01, hc23, hlam, hphi, ht12, p11670_1]
                          · have p11670_0 := h11670c.1
                            have p11670_1 := h11670c.2.1
                            have p11670_2 := h11670c.2.2.1
                            have p11670_3 := h11670c.2.2.2
                            linarith only [hlam, p11670_0]
                      · linarith only [h0, h10364, h11603, h11662, h11664, h11667, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h10364, h11601, h11603, h11662, h11664, h11666, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10364, h11080, h11601, h11603, h11662, h11664, h11665, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11699 | h11699
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11700 | h11700
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11701 | h11701
                      · linarith only [h11664, h11701, h6681, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h11658, h11701, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h11603, h11663, h11700, hlam]
                  · linarith only [h11080, h11081, h11603, h11663, h11699, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11706 | h11706
                · linarith only [h0, h10364, h11601, h11662, h11663, h11706, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11708 | h11708
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h11709 | h11709
                    · linarith only [h11663, h11709, h4610, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h11603, h11709, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h11080, h11603, h11708, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h11080, h11662, h4610, hlam]

end R2N4
