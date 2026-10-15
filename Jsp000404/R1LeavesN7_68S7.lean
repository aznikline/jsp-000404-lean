import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_24_L_R_H_I_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h10, h12, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h10, h11, h12, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h11, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h0, h10, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h17, h18, h6, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h0, h17, h20, h6, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · rcases h4bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h2, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p22_1, u2ehi3]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p22_1, u2ehi3]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            rcases p22_3 (m.d 0 4) (by simp) with h26 | h26
                            · rcases p22_3 (m.d 1 4) (by simp) with h27 | h27
                              · linarith only [h1, h27, hlam]
                              · linarith only [h27, h8, hlam]
                            · linarith only [h26, h4, hlam]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h2, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p22_1, u2ehi3]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h1, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p22_1, u2ehi3]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h2, h4, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h9, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h3, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h7, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h18, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h4, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h8, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h17, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h20, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h5, hlam, p22_0]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h2, h4, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h2, h4, h5, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [h0, h2, h4, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22_1]
                          · have p22_0 := h22c.1
                            have p22_1 := h22c.2.1
                            have p22_2 := h22c.2.2.1
                            have p22_3 := h22c.2.2.2
                            linarith only [hlam, p22_0]
                    · linarith only [h0, h17, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                    · linarith only [h54, h6, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h57 | h57
                        · rcases h4bigk with h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, h2, h4, h54, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p58_1, u2ehi2]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, h2, h4, h54, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p58_1, u2ehi2]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, h2, h4, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p58_1, u2ehi2]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            rcases p58_3 (m.d 0 4) (by simp) with h63 | h63
                            · rcases p58_3 (m.d 1 4) (by simp) with h64 | h64
                              · linarith only [h1, h64, hlam]
                              · linarith only [h53, h64, hlam]
                            · linarith only [h63, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h1, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h54, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p58_1, u2ehi2]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h8, hlam, p58_1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, h2, h4, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p58_1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h3, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h7, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h54, hlam, p58_1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p58_1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h4, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, h2, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p58_1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, h2, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p58_1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, h2, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p58_1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h5, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h53, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h56, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h57, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hlam, p58_0]
                        · linarith only [h0, h2, h4, h5, h57, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1, h53, h56, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                    · linarith only [h6, h8, h90, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                      · linarith only [h0, h53, h7, h92, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
                        · linarith only [h53, h6, h8, h94, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h6, h8, h94, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h0, h3, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h98 | h98
              · linarith only [h6, h98, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h104 | h104
                        · rcases h4bigk with h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h0, h2, h4, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi1]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi3]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h0, h104, h2, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            rcases p105_3 (m.d 0 4) (by simp) with h110 | h110
                            · rcases p105_3 (m.d 1 4) (by simp) with h111 | h111
                              · linarith only [h1, h111, hlam]
                              · linarith only [h101, h111, hlam]
                            · linarith only [h110, hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h1, hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h98, hlam, p105_1]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h104, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p105_1]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h0, h100, h2, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h3, hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h0, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p105_1]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h0, h102, h104, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h0, h102, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h4, hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h100, hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h102, hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h0, h2, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h5, hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h101, hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h103, hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [h104, hlam, p105_0]
                          · have p105_0 := h105c.1
                            have p105_1 := h105c.2.1
                            have p105_2 := h105c.2.2.1
                            have p105_3 := h105c.2.2.2
                            linarith only [hlam, p105_0]
                        · rcases h4bigk with h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h0, h101, h104, h2, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p135_1, u2ehi3]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            rcases p135_3 (m.d 0 4) (by simp) with h139 | h139
                            · rcases p135_3 (m.d 1 4) (by simp) with h140 | h140
                              · linarith only [h1, h140, hlam]
                              · linarith only [h100, h140, hlam]
                            · linarith only [h139, h4, hlam]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h0, h104, h2, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h1, hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h98, hlam, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h0, h100, h104, h2, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h3, hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h0, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h0, h102, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h0, h102, h104, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h4, hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h100, hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h102, hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h104, hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h5, hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h101, hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h103, hlam, p135_0]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [h101, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p135_1]
                          · have p135_0 := h135c.1
                            have p135_1 := h135c.2.1
                            have p135_2 := h135c.2.2.1
                            have p135_3 := h135c.2.2.2
                            linarith only [hlam, p135_0]
                      · linarith only [h101, h103, h98, hlam]
                    · linarith only [h0, h102, h2, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h168 | h168
                      · linarith only [h101, h167, h168, h98, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h168, h2, h4, h5, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                    · linarith only [h167, h6, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                    · linarith only [h0, h100, h173, h2, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                    · linarith only [h173, h6, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h176 | h176
                    · linarith only [h100, h176, h6, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h0, h176, h2, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
            · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
              · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
                · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                  · linarith only [h1, h182, h5, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                      · linarith only [h0, h179, h184, h185, h5, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                        · linarith only [h0, h1, h179, h180, h184, h187, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · rcases h4bigk with h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h180, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p189_1, u2ehi3]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h5, hc45, hlam, hphi, ht23, ht34, p189_1, u2ehi3]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h5, hc34, hc45, hlam, hphi, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h5, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h1, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p189_1, u2ehi3]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h1, h5, hc34, hc45, hlam, hphi, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h182, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h3, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h180, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h0, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h185, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h4, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h181, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h184, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h187, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hc04, hc45, hlam, hphi, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hc14, hc45, hlam, hphi, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hc45, hlam, hphi, ht23, ht34, p189_1, u2ehi3]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hc34, hc45, hlam, hphi, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hlam, p189_0]
                    · linarith only [h184, h4, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h179, h181, h4, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h180, h3, h5, hc45, hlam, hphi, ht23, ht34, u2ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
              · linarith only [h179, h218, hc23, hlam, hphi, u2ehi3]
              · linarith only [h218, h3, h5, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h221 | h221
          · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
            · rcases m.htr 1 2 4 (by decide) (by decide) with h223 | h223
              · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                · linarith only [h0, h2, h222, h224, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                    · linarith only [h2, h227, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h229 | h229
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h230 | h230
                        · rcases h4bigk with h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h223, h229, hc04, hc45, hlam, hphi, ht0b, ht5b, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p231_1, u2ehi3]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h4, hlam, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            rcases p231_3 (m.d 0 4) (by simp) with h236 | h236
                            · rcases p231_3 (m.d 1 4) (by simp) with h237 | h237
                              · linarith only [h1, h237, hlam]
                              · linarith only [h226, h237, hlam]
                            · linarith only [h236, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h1, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h227, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p231_1, u2ehi2]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h224, hlam, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h0, h223, hc01, hc45, hlam, hphi, ht0b, ht5b, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h3, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h223, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h227, hlam, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h3, hc34, hlam, hphi, ht23, p231_1, u2ehi3]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h223, h229, hc34, hlam, hphi, ht23, p231_1, u2ehi4]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h229, hc34, hlam, hphi, ht23, p231_1, u2ehi4]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            rcases p231_3 (m.d 0 4) (by simp) with h255 | h255
                            · linarith only [h255, h4, hlam]
                            · linarith only [h221, h255, hlam]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h221, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h226, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h229, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h230, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                        · linarith only [h2, h230, h4, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h1, h226, h229, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h221, h223, h226, h4, hc34, hlam, hphi, ht23, u2ehi3]
              · linarith only [h0, h222, h223, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h2, h222, h4, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
            · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
              · rcases m.htr 1 3 4 (by decide) (by decide) with h270 | h270
                · linarith only [h0, h2, h268, h270, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h272 | h272
                  · linarith only [h1, h221, h272, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                    · linarith only [h2, h274, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h276 | h276
                      · linarith only [h0, h221, h269, h276, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h278 | h278
                        · linarith only [h1, h221, h268, h270, h278, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h2, h278, h4, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h221, h269, h3, hc45, hlam, hphi, ht23, ht34, u2ehi1]
            · linarith only [h2, h268, h4, hc34, hlam, hphi, ht23, u2ehi1]
      · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h284 | h284
      · linarith only [h2, h284, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h286 | h286
        · rcases m.htr 0 4 5 (by decide) (by decide) with h287 | h287
          · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
            · linarith only [h0, h2, h288, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h290 | h290
              · linarith only [h0, h284, h290, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h292 | h292
                · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h295 | h295
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h296 | h296
                        · rcases h4bigk with h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c | h297c
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h292, h296, hc04, hc45, hlam, hphi, ht0b, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h284, hlam, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h284, h294, h296, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            rcases p297_3 (m.d 0 4) (by simp) with h302 | h302
                            · rcases p297_3 (m.d 1 4) (by simp) with h303 | h303
                              · linarith only [h1, h303, hlam]
                              · linarith only [h293, h303, hlam]
                            · linarith only [h302, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h1, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h290, hlam, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h296, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h284, h294, hc23, hlam, hphi, p297_1, u2ehi0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h290, h294, hc23, hlam, hphi, p297_1, u2ehi1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h294, h296, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            rcases p297_3 (m.d 0 4) (by simp) with h316 | h316
                            · linarith only [h284, h316, hlam]
                            · linarith only [h287, h316, hlam]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h286, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h292, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h294, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h286, hc03, hc45, hlam, hphi, ht0b, ht5b, p297_1]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h287, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h293, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h295, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [h296, hlam, p297_0]
                          · have p297_0 := h297c.1
                            have p297_1 := h297c.2.1
                            have p297_2 := h297c.2.2.1
                            have p297_3 := h297c.2.2.2
                            linarith only [hlam, p297_0]
                        · rcases h4bigk with h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c | h329c
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h293, h296, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p329_1]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h284, hlam, p329_1]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            rcases p329_3 (m.d 0 4) (by simp) with h333 | h333
                            · rcases p329_3 (m.d 1 4) (by simp) with h334 | h334
                              · linarith only [h1, h334, hlam]
                              · linarith only [h292, h334, hlam]
                            · linarith only [h286, h333, hlam]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h284, h294, h296, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p329_1]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h1, hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h290, hlam, p329_1]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p329_1]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h1, h296, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p329_1]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h0, h284, h294, hc23, hlam, hphi, p329_1, u2ehi1]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h290, h294, hc23, hlam, hphi, p329_1, u2ehi1]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            rcases p329_3 (m.d 0 4) (by simp) with h347 | h347
                            · linarith only [h284, h347, hlam]
                            · linarith only [h286, h347, hlam]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h294, h296, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p329_1]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h286, hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h292, hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h294, hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h296, hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h287, hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h293, hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h295, hlam, p329_0]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [h1, h293, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p329_1]
                          · have p329_0 := h329c.1
                            have p329_1 := h329c.2.1
                            have p329_2 := h329c.2.2.1
                            have p329_3 := h329c.2.2.2
                            linarith only [hlam, p329_0]
                      · linarith only [h1, h293, h295, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h0, h2, h294, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h2, h286, h287, h290, h293, hc23, hlam, hphi, u2ehi1]
                · linarith only [h2, h286, h288, h292, hc23, hlam, hphi, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h365 | h365
            · linarith only [h0, h284, h365, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h367 | h367
              · linarith only [h0, h284, h287, h367, hc45, hlam, hphi, ht23, ht34, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h369 | h369
                · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
                  · linarith only [h1, h284, h287, h370, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h372 | h372
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h373 | h373
                      · linarith only [h0, h284, h287, h372, h373, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h284, h373, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                    · linarith only [h0, h2, h369, h372, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                · linarith only [h2, h286, h365, h369, hc23, hlam, hphi, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h378 | h378
          · rcases m.htr 1 2 3 (by decide) (by decide) with h379 | h379
            · linarith only [h0, h284, h379, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h381 | h381
              · linarith only [h0, h284, h381, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h383 | h383
                · linarith only [h2, h286, h379, h383, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h385 | h385
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                    · linarith only [h0, h2, h286, h386, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h0, h2, h386, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h286, h378, h379, h383, h385, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h390 | h390
            · linarith only [h0, h2, h390, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h392 | h392
              · linarith only [h0, h2, h392, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h394 | h394
                · linarith only [h2, h286, h390, h394, hc23, hlam, hphi, u2ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h396 | h396
                  · linarith only [h0, h1, h2, h286, h378, h396, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h398 | h398
                    · linarith only [h0, h2, h286, h398, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h0, h2, h398, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h401 | h401
    · rcases m.htr 0 2 4 (by decide) (by decide) with h402 | h402
      · linarith only [h0, h1, h402, hlam]
      · linarith only [h401, h402, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h405 | h405
      · linarith only [h401, h405, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h407 | h407
        · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
          · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
            · linarith only [h0, h1, h401, h407, h409, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h411 | h411
              · linarith only [h0, h1, h411, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h1, h411, hc24, hlam, hphi, u2ehi1]
          · linarith only [h0, h1, h408, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h415 | h415
          · rcases m.htr 1 2 3 (by decide) (by decide) with h416 | h416
            · linarith only [h0, h1, h416, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h418 | h418
              · linarith only [h0, h1, h418, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h0, h1, h418, hc24, hlam, hphi, u2ehi1]
          · linarith only [h0, h1, h415, hc45, hlam, hphi, ht23, ht34, u2ehi1]

end R2N4
