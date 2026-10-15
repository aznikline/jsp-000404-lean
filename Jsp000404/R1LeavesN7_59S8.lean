import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3542000 in
set_option maxHeartbeats 3542000 in
theorem r1l7_20_11_14_M_LR_L_I_L_I_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
            · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h11, h7, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                    · linarith only [h0, h14, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h14, h7, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h18, h3, h9, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                      · linarith only [h0, h20, h8, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h17, h2, h20, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                    · linarith only [h0, h23, h7, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                      · linarith only [h0, h17, h25, h4, h9, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                        · linarith only [h0, h17, h27, h3, h5, h7, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h27, h3, h5, h6, h7, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h4, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
              · linarith only [h0, h3, h31, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                        · linarith only [h1, h33, h37, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h2, h34, h37, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h31, h34, h36, hlam]
                    · linarith only [h0, h3, h35, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                      · linarith only [h0, h3, h34, h42, h43, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h3, h31, h43, h5, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h1, h33, h42, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                    · linarith only [h0, h3, h33, h48, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h3, h48, h5, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                    · linarith only [h0, h3, h33, h51, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h3, h5, h51, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
            · rcases m.htr 1 2 4 (by decide) (by decide) with h55 | h55
              · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                  · linarith only [h57, h6, hc14, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
                    · linarith only [h0, h54, h59, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h54, h56, h59, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                  · linarith only [h0, h3, h5, h56, h6, h62, hlam, hphi, u0ehi8, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                    · linarith only [h0, h3, h56, h64, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
                      · linarith only [h0, h55, h6, h66, hlam, hphi, u0ehi8, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h68 | h68
                        · linarith only [h6, h68, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                        · rcases h4bigk with h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h6, hc14, hc45, hlam, hphi, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h6, hc24, hc45, hlam, hphi, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h54, h56, h6, hc23, hc45, hlam, hphi, ht34, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h6, hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h2, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h2, hc24, hlam, hphi, ht0b, ht45, ht5b, p70_1, u0elo0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h56, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h62, hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h4, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h55, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h64, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h66, hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h5, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h0, h3, h5, hc14, hlam, hphi, ht0b, ht45, ht5b, p70_1, u0elo0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h0, h3, h5, hc24, hlam, hphi, ht0b, ht45, ht5b, p70_1, u0elo0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h68, hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h0, h3, h5, h54, h56, hc23, hc45, hlam, hphi, ht34, p70_1, u0ehi8, u0elo0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            rcases p70_3 (m.d 0 4) (by simp) with h92 | h92
                            · linarith only [h6, h92, hlam]
                            · linarith only [h2, h92, hlam]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            rcases p70_3 (m.d 0 4) (by simp) with h95 | h95
                            · linarith only [h6, h95, hlam]
                            · linarith only [h4, h95, hlam]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h54, h56, hc23, hc45, hlam, hphi, ht34, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [hlam, p70_0]
              · linarith only [h0, h4, h54, h55, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
              · linarith only [h0, h101, h3, h54, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h103 | h103
                · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                  · linarith only [h104, h6, hc14, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h107 | h107
                      · linarith only [h0, h106, h107, h3, h6, hlam, hphi, u0ehi8, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h109 | h109
                        · linarith only [h109, h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                        · rcases h4bigk with h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c | h111c
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [hlam, p111_0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h6, hc14, hc45, hlam, hphi, p111_1]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h101, h6, hc12, hc45, hlam, hphi, ht23, ht34, p111_1]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h6, hc34, hc45, hlam, hphi, p111_1]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h6, hlam, p111_0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h2, hlam, p111_1]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [hlam, p111_0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h101, hlam, p111_0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h2, hc34, hlam, hphi, ht0b, ht45, ht5b, p111_1, u0elo0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h104, hlam, p111_0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h4, hlam, p111_1]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h0, h4, hc14, hlam, hphi, ht0b, ht45, ht5b, p111_1, u0elo0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [hlam, p111_0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h0, h106, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p111_1, u0elo0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h107, hlam, p111_0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h5, hlam, p111_1]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h103, hlam, p111_0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h106, hlam, p111_0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [hlam, p111_0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h109, hlam, p111_0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h0, h101, h106, h3, hc12, hc45, hlam, hphi, ht23, ht34, p111_1, u0ehi8, u0elo0]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            rcases p111_3 (m.d 0 4) (by simp) with h133 | h133
                            · linarith only [h133, h6, hlam]
                            · linarith only [h133, h2, hlam]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [h101, hc12, hc45, hlam, hphi, ht23, ht34, p111_1]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            rcases p111_3 (m.d 0 4) (by simp) with h137 | h137
                            · linarith only [h137, h6, hlam]
                            · linarith only [h137, h5, hlam]
                          · have p111_0 := h111c.1
                            have p111_1 := h111c.2.1
                            have p111_2 := h111c.2.2.1
                            have p111_3 := h111c.2.2.2
                            linarith only [hlam, p111_0]
                    · linarith only [h0, h106, h3, h5, h54, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h142 | h142
                  · linarith only [h142, h6, hc14, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                    · linarith only [h0, h103, h144, h3, h54, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h144, h3, h5, h54, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h147 | h147
          · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
            · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
              · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                · linarith only [h150, h5, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                    · linarith only [h148, h153, h5, hc12, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h155 | h155
                      · linarith only [h0, h149, h155, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h0, h149, h152, h153, h155, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h158 | h158
                    · linarith only [h158, h5, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                      · linarith only [h0, h150, h152, h160, h4, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h162 | h162
                        · rcases h4bigk with h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            rcases p163_3 (m.d 0 4) (by simp) with h165 | h165
                            · rcases p163_3 (m.d 1 4) (by simp) with h166 | h166
                              · linarith only [h166, h2, hlam]
                              · rcases p163_3 (m.d 2 4) (by simp) with h168 | h168
                                · linarith only [h168, h4, hlam]
                                · rcases p163_3 (m.d 3 4) (by simp) with h170 | h170
                                  · rcases p163_3 (m.d 4 5) (by simp) with h171 | h171
                                    · linarith only [h147, h171, hlam]
                                    · linarith only [h152, h171, hlam]
                                  · linarith only [h150, h170, hlam]
                            · linarith only [h165, h2, hlam]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            rcases p163_3 (m.d 0 4) (by simp) with h176 | h176
                            · rcases p163_3 (m.d 1 4) (by simp) with h177 | h177
                              · linarith only [h177, h2, hlam]
                              · linarith only [h149, h177, hlam]
                            · linarith only [h176, h4, hlam]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h5, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h0, h148, h150, h152, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p163_1, u0elo0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h2, hlam, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h152, hc24, hc45, hlam, hphi, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h150, hlam, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h152, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h4, hlam, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h149, hlam, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h158, hlam, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h160, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p163_1, u0ehi8]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            rcases p163_3 (m.d 0 4) (by simp) with h194 | h194
                            · linarith only [h194, h5, hlam]
                            · linarith only [h194, h2, hlam]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            rcases p163_3 (m.d 0 4) (by simp) with h197 | h197
                            · linarith only [h197, h5, hlam]
                            · linarith only [h197, h4, hlam]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h148, h150, h152, hc23, hc34, hlam, hphi, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h147, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h0, h147, h148, h150, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p163_1, u0elo0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h0, h147, h158, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p163_1, u0elo0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h162, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [hlam, p163_0]
                        · linarith only [h0, h147, h162, h4, h5, hlam, hphi, u0ehi7, u0elo0]
              · linarith only [h0, h148, h149, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h209 | h209
              · linarith only [h0, h148, h209, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h211 | h211
                · linarith only [h211, h5, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h213 | h213
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h214 | h214
                    · linarith only [h0, h214, h3, h5, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h216 | h216
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h217 | h217
                        · rcases h4bigk with h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c | h218c
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [hlam, p218_0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h0, h213, h4, hc45, hlam, hphi, ht0b, ht5b, p218_1, u0elo0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h0, h148, h214, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p218_1, u0elo0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h5, hlam, p218_0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            rcases p218_3 (m.d 0 4) (by simp) with h223 | h223
                            · rcases p218_3 (m.d 1 4) (by simp) with h224 | h224
                              · linarith only [h2, h224, hlam]
                              · linarith only [h213, h224, hlam]
                            · linarith only [h223, hlam, p218_0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h2, hlam, p218_1]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [hlam, p218_0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h209, hlam, p218_0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h211, hlam, p218_1]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p218_1, u0elo0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h4, hlam, p218_1]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h0, h4, hc14, hlam, hphi, ht0b, ht45, ht5b, p218_1, u0elo0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [hlam, p218_0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h214, hlam, p218_1]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h0, h4, hc45, hlam, hphi, ht0b, ht5b, p218_1, u0elo0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h0, h148, h214, h4, hc12, hc34, hlam, hphi, ht23, p218_1, u0ehi8, u0elo0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            rcases p218_3 (m.d 0 4) (by simp) with h239 | h239
                            · linarith only [h239, h5, hlam]
                            · linarith only [h2, h239, hlam]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h148, h214, hc12, hc34, hlam, hphi, ht23, p218_1]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [hlam, p218_0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            rcases p218_3 (m.d 0 4) (by simp) with h244 | h244
                            · linarith only [h244, h5, hlam]
                            · linarith only [h147, h244, hlam]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h147, hlam, p218_0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h213, hlam, p218_0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h216, hlam, p218_0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [h217, hlam, p218_0]
                          · have p218_0 := h218c.1
                            have p218_1 := h218c.2.1
                            have p218_2 := h218c.2.2.1
                            have p218_3 := h218c.2.2.2
                            linarith only [hlam, p218_0]
                        · linarith only [h2, h213, h217, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h209, h213, h216, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
                    · linarith only [h0, h147, h148, h211, h213, h254, h4, h5, hc12, hc23, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h256 | h256
                      · linarith only [h0, h148, h211, h213, h256, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h147, h148, h254, h256, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h259 | h259
            · rcases m.htr 1 2 4 (by decide) (by decide) with h260 | h260
              · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
                · linarith only [h261, h5, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h263 | h263
                  · linarith only [h147, h260, h263, hc12, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h265 | h265
                    · linarith only [h265, h5, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h267 | h267
                      · linarith only [h147, h267, h5, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h269 | h269
                        · linarith only [h147, h269, h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                        · linarith only [h269, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h0, h259, h260, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
              · linarith only [h0, h259, h273, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h275 | h275
                · linarith only [h275, h5, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
                  · linarith only [h0, h147, h273, h277, h4, h5, hlam, hphi, u0ehi7, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                    · linarith only [h0, h279, h3, h5, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h281 | h281
                      · linarith only [h0, h147, h281, h4, h5, hlam, hphi, u0ehi7, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h283 | h283
                        · linarith only [h147, h283, h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                        · linarith only [h0, h259, h279, h283, h4, h5, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi7, u0elo0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h286 | h286
        · linarith only [h286, h3, h4, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h288 | h288
          · rcases m.htr 1 2 3 (by decide) (by decide) with h289 | h289
            · rcases m.htr 1 2 4 (by decide) (by decide) with h290 | h290
              · linarith only [h290, h4, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h292 | h292
                · linarith only [h286, h292, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h294 | h294
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h295 | h295
                    · linarith only [h286, h295, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h297 | h297
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h298 | h298
                        · rcases h4bigk with h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h289, h290, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p299_1, u0elo3]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h4, hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h286, hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            rcases p299_3 (m.d 0 4) (by simp) with h304 | h304
                            · rcases p299_3 (m.d 1 4) (by simp) with h305 | h305
                              · linarith only [h2, h305, hlam]
                              · linarith only [h294, h305, hlam]
                            · linarith only [h304, hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h2, hlam, p299_1]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h290, hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h292, hlam, p299_1]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p299_1, u0elo0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p299_1, u0ehi8]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h289, h290, h295, hc23, hc34, hlam, hphi, p299_1]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h295, hlam, p299_1]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            rcases p299_3 (m.d 0 4) (by simp) with h318 | h318
                            · linarith only [h318, h4, hlam]
                            · linarith only [h288, h318, hlam]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h3, h4, hc34, hlam, hphi, ht01, ht12, ht23, p299_1, u0ehi7]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h289, h290, hc23, hc34, hlam, hphi, p299_1]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h3, h4, hc34, hlam, hphi, ht01, ht12, ht23, p299_1, u0ehi7]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            rcases p299_3 (m.d 0 4) (by simp) with h325 | h325
                            · linarith only [h286, h325, hlam]
                            · linarith only [h288, h325, hlam]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h288, hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h294, hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h297, hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [h298, hlam, p299_0]
                          · have p299_0 := h299c.1
                            have p299_1 := h299c.2.1
                            have p299_2 := h299c.2.2.1
                            have p299_3 := h299c.2.2.2
                            linarith only [hlam, p299_0]
                        · linarith only [h286, h298, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                      · linarith only [h294, h297, h3, h4, hc14, hlam, hphi, ht01, u0ehi7]
                  · linarith only [h288, h289, h290, h294, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
            · linarith only [h289, h3, h4, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h337 | h337
            · rcases m.htr 1 2 4 (by decide) (by decide) with h338 | h338
              · linarith only [h0, h3, h338, h4, hlam, hphi, u0ehi7, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
                · linarith only [h286, h340, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h342 | h342
                  · linarith only [h2, h288, h3, h342, h4, hlam, hphi, u0ehi7, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h344 | h344
                    · linarith only [h2, h286, h337, h338, h344, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h346 | h346
                      · linarith only [h288, h3, h346, h4, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                      · linarith only [h3, h346, h4, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
            · linarith only [h3, h337, h4, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h350 | h350
      · rcases m.htr 0 3 4 (by decide) (by decide) with h351 | h351
        · rcases m.htr 0 4 5 (by decide) (by decide) with h352 | h352
          · rcases m.htr 1 2 3 (by decide) (by decide) with h353 | h353
            · linarith only [h3, h353, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h355 | h355
              · rcases m.htr 1 3 4 (by decide) (by decide) with h356 | h356
                · rcases m.htr 1 4 5 (by decide) (by decide) with h357 | h357
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h358 | h358
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h359 | h359
                      · linarith only [h0, h355, h359, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h1, h353, h355, h357, h358, h359, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h3, h350, h352, h358, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h364 | h364
                      · linarith only [h355, h357, h364, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h366 | h366
                        · linarith only [h355, h357, h363, h366, hlam]
                        · rcases h4bigk with h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [hlam, p368_0]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            rcases p368_3 (m.d 0 4) (by simp) with h370 | h370
                            · rcases p368_3 (m.d 1 4) (by simp) with h371 | h371
                              · linarith only [h2, h371, hlam]
                              · rcases p368_3 (m.d 2 4) (by simp) with h373 | h373
                                · linarith only [h350, h373, hlam]
                                · rcases p368_3 (m.d 3 4) (by simp) with h375 | h375
                                  · linarith only [h351, h375, hlam]
                                  · rcases p368_3 (m.d 4 5) (by simp) with h377 | h377
                                    · linarith only [h352, h377, hlam]
                                    · linarith only [h357, h377, hlam]
                            · linarith only [h2, h370, hlam]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            rcases p368_3 (m.d 0 4) (by simp) with h381 | h381
                            · rcases p368_3 (m.d 1 4) (by simp) with h382 | h382
                              · linarith only [h2, h382, hlam]
                              · linarith only [h355, h382, hlam]
                            · linarith only [h350, h381, hlam]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            rcases p368_3 (m.d 0 4) (by simp) with h386 | h386
                            · rcases p368_3 (m.d 1 4) (by simp) with h387 | h387
                              · linarith only [h2, h387, hlam]
                              · linarith only [h356, h387, hlam]
                            · linarith only [h351, h386, hlam]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h350, h355, h357, h363, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1, u0elo1]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h2, hlam, p368_1]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [hlam, p368_0]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h357, h363, hc34, hc45, hlam, hphi, p368_1]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h1, h353, h355, hc34, hlam, hphi, ht0b, ht45, ht5b, p368_1, u0elo0]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h357, hlam, p368_0]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h350, hlam, p368_1]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h355, hlam, p368_1]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [hlam, p368_0]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h3, h350, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p368_1]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h364, hlam, p368_0]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h351, hlam, p368_1]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h356, hlam, p368_0]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h363, hlam, p368_0]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [hlam, p368_0]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h366, hlam, p368_0]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h352, hlam, p368_0]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h3, h350, h352, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p368_1]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h3, h350, h352, h363, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p368_1]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [h3, h350, h352, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p368_1]
                          · have p368_0 := h368c.1
                            have p368_1 := h368c.2.1
                            have p368_2 := h368c.2.2.1
                            have p368_3 := h368c.2.2.2
                            linarith only [hlam, p368_0]
                    · linarith only [h3, h363, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · linarith only [h1, h351, h353, h355, h356, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h3, h350, h355, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h415 | h415
            · linarith only [h3, h415, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h417 | h417
              · rcases m.htr 1 3 4 (by decide) (by decide) with h418 | h418
                · rcases m.htr 1 4 5 (by decide) (by decide) with h419 | h419
                  · linarith only [h352, h419, hc14, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h421 | h421
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h422 | h422
                      · linarith only [h1, h352, h415, h417, h422, hlam, hphi, u0ehi8, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h424 | h424
                        · linarith only [h1, h352, h415, h417, h421, h424, hlam, hphi, u0ehi8, u0elo0]
                        · rcases h4bigk with h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [hlam, p426_0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h352, hc14, hc45, hlam, hphi, p426_1]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h352, hc24, hc45, hlam, hphi, p426_1]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h352, hc34, hc45, hlam, hphi, p426_1]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h352, hlam, p426_0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h2, hlam, p426_1]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [hlam, p426_0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h2, h421, hc34, hlam, hphi, ht0b, ht45, ht5b, p426_1, u0elo0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h1, h415, h417, hc34, hlam, hphi, ht0b, ht45, ht5b, p426_1, u0elo0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h419, hlam, p426_0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h350, hlam, p426_1]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h417, hlam, p426_1]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [hlam, p426_0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h350, hc34, hlam, hphi, ht0b, ht45, ht5b, p426_1, u0elo1]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h422, hlam, p426_0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h351, hlam, p426_1]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h418, hlam, p426_0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h421, hlam, p426_0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [hlam, p426_0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [h424, hlam, p426_0]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p426_1, u0ehi8]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            rcases p426_3 (m.d 0 4) (by simp) with h448 | h448
                            · linarith only [h352, h448, hlam]
                            · linarith only [h2, h448, hlam]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            rcases p426_3 (m.d 0 4) (by simp) with h451 | h451
                            · linarith only [h352, h451, hlam]
                            · linarith only [h350, h451, hlam]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            rcases p426_3 (m.d 0 4) (by simp) with h454 | h454
                            · linarith only [h352, h454, hlam]
                            · linarith only [h351, h454, hlam]
                          · have p426_0 := h426c.1
                            have p426_1 := h426c.2.1
                            have p426_2 := h426c.2.2.1
                            have p426_3 := h426c.2.2.2
                            linarith only [hlam, p426_0]
                    · linarith only [h3, h421, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · linarith only [h1, h351, h415, h417, h418, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h3, h350, h417, hc12, hc23, hlam, hphi]
        · linarith only [h3, h350, h351, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h462 | h462
        · rcases m.htr 0 4 5 (by decide) (by decide) with h463 | h463
          · rcases m.htr 1 2 3 (by decide) (by decide) with h464 | h464
            · linarith only [h3, h464, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h466 | h466
              · linarith only [h350, h466, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h468 | h468
                · rcases m.htr 1 4 5 (by decide) (by decide) with h469 | h469
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h470 | h470
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h471 | h471
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h472 | h472
                        · linarith only [h1, h468, h472, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h1, h468, h469, h472, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h350, h468, h469, h471, hlam, hphi, u0ehi6, u0elo0]
                    · linarith only [h3, h470, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h479 | h479
                        · linarith only [h1, h466, h468, h469, h479, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases h4bigk with h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            rcases p481_3 (m.d 0 4) (by simp) with h483 | h483
                            · rcases p481_3 (m.d 1 4) (by simp) with h484 | h484
                              · linarith only [h2, h484, hlam]
                              · rcases p481_3 (m.d 2 4) (by simp) with h486 | h486
                                · rcases p481_3 (m.d 3 4) (by simp) with h487 | h487
                                  · linarith only [h462, h487, hlam]
                                  · rcases p481_3 (m.d 4 5) (by simp) with h489 | h489
                                    · linarith only [h463, h489, hlam]
                                    · linarith only [h469, h489, hlam]
                                · linarith only [h466, h486, hlam]
                            · linarith only [h2, h483, hlam]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h350, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            rcases p481_3 (m.d 0 4) (by simp) with h495 | h495
                            · rcases p481_3 (m.d 1 4) (by simp) with h496 | h496
                              · linarith only [h2, h496, hlam]
                              · linarith only [h468, h496, hlam]
                            · linarith only [h462, h495, hlam]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h1, h462, h466, h469, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p481_1, u0elo0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h2, hlam, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h466, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h469, hc34, hc45, hlam, hphi, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h469, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h477, hc23, hlam, hphi, ht01, ht12, p481_1, u0ehi8]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            rcases p481_3 (m.d 0 4) (by simp) with h507 | h507
                            · linarith only [h350, h507, hlam]
                            · linarith only [h2, h507, hlam]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            rcases p481_3 (m.d 0 4) (by simp) with h511 | h511
                            · linarith only [h350, h511, hlam]
                            · linarith only [h462, h511, hlam]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h466, h469, h477, hc12, hc23, hlam, hphi, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h462, hlam, p481_1]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h468, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h477, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h479, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h463, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h1, h462, h463, h466, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p481_1, u0elo0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h478, hlam, p481_0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [h1, h462, h463, hc34, hlam, hphi, ht0b, ht45, ht5b, p481_1, u0elo0]
                          · have p481_0 := h481c.1
                            have p481_1 := h481c.2.1
                            have p481_2 := h481c.2.2.1
                            have p481_3 := h481c.2.2.2
                            linarith only [hlam, p481_0]
                      · linarith only [h1, h350, h462, h463, h478, hlam, hphi, u0ehi6, u0elo0]
                    · linarith only [h3, h477, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h527 | h527
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h528 | h528
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h529 | h529
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h530 | h530
                        · rcases h4bigk with h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h1, h462, h527, hc45, hlam, hphi, ht0b, ht5b, p531_1, u0elo0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h350, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h1, h462, h464, h468, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p531_1, u0elo0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            rcases p531_3 (m.d 0 4) (by simp) with h536 | h536
                            · rcases p531_3 (m.d 1 4) (by simp) with h537 | h537
                              · linarith only [h2, h537, hlam]
                              · linarith only [h527, h537, hlam]
                            · linarith only [h536, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h2, hlam, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h466, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h468, hlam, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, ht0b, ht5b, p531_1, u0elo0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h528, hc23, hlam, hphi, ht01, ht12, p531_1, u0ehi8]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            rcases p531_3 (m.d 0 4) (by simp) with h547 | h547
                            · linarith only [h350, h547, hlam]
                            · linarith only [h2, h547, hlam]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h464, h468, h528, hc12, hc23, hlam, hphi, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            rcases p531_3 (m.d 0 4) (by simp) with h552 | h552
                            · linarith only [h350, h552, hlam]
                            · linarith only [h463, h552, hlam]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h462, hlam, p531_1]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h1, h462, hc14, hlam, hphi, ht0b, ht45, ht5b, p531_1, u0elo0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h528, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h1, h462, hc45, hlam, hphi, ht0b, ht5b, p531_1, u0elo0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h463, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h527, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h529, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [h530, hlam, p531_0]
                          · have p531_0 := h531c.1
                            have p531_1 := h531c.2.1
                            have p531_2 := h531c.2.2.1
                            have p531_3 := h531c.2.2.2
                            linarith only [hlam, p531_0]
                        · linarith only [h2, h464, h468, h527, h530, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h1, h462, h468, h527, h529, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h1, h3, h462, h528, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h569 | h569
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h570 | h570
                        · linarith only [h1, h462, h527, h570, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h462, h463, h464, h468, h570, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h1, h350, h462, h463, h569, hlam, hphi, u0ehi6, u0elo0]
                    · linarith only [h3, h568, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h575 | h575
            · linarith only [h3, h575, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h577 | h577
              · linarith only [h350, h577, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h579 | h579
                · rcases m.htr 1 4 5 (by decide) (by decide) with h580 | h580
                  · linarith only [h1, h463, h579, h580, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h582 | h582
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h583 | h583
                      · linarith only [h350, h463, h582, h583, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h350, h583, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h1, h579, h582, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h587 | h587
                  · linarith only [h350, h463, h587, hc14, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h589 | h589
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h590 | h590
                      · linarith only [h350, h463, h589, h590, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h1, h350, h462, h575, h579, h590, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi6, u0elo0]
                    · linarith only [h1, h3, h462, h589, hlam, hphi, u0ehi6, u0elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h594 | h594
          · rcases m.htr 1 2 3 (by decide) (by decide) with h595 | h595
            · linarith only [h3, h595, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h597 | h597
              · linarith only [h350, h597, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h599 | h599
                · linarith only [h1, h462, h599, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h601 | h601
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h602 | h602
                    · linarith only [h3, h462, h602, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h3, h602, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h605 | h605
                    · linarith only [h2, h3, h462, h594, h595, h599, h601, h605, hc12, hc23, hlam, hphi, u0ehi6, u0elo0]
                    · linarith only [h2, h3, h594, h595, h599, h601, h605, hc12, hc34, hlam, hphi, ht23, u0ehi6, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h608 | h608
            · linarith only [h3, h608, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h610 | h610
              · linarith only [h1, h350, h608, h610, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h612 | h612
                · linarith only [h1, h3, h462, h612, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h614 | h614
                  · linarith only [h2, h594, h614, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h616 | h616
                    · linarith only [h3, h462, h616, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h3, h616, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h619 | h619
    · rcases m.htr 0 2 4 (by decide) (by decide) with h620 | h620
      · linarith only [h0, h2, h620, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h622 | h622
        · linarith only [h1, h2, h622, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h624 | h624
          · rcases m.htr 1 2 3 (by decide) (by decide) with h625 | h625
            · rcases m.htr 1 2 4 (by decide) (by decide) with h626 | h626
              · linarith only [h0, h2, h620, h626, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h628 | h628
                · linarith only [h0, h2, h622, h625, h626, h628, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                · linarith only [h0, h2, h625, h628, hc23, hc34, hlam, hphi]
            · linarith only [h619, h620, h625, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h632 | h632
            · linarith only [h0, h2, h624, h632, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h2, h619, h624, h632, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h635 | h635
      · linarith only [h1, h2, h619, h635, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h637 | h637
        · linarith only [h1, h2, h637, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h639 | h639
          · rcases m.htr 1 2 3 (by decide) (by decide) with h640 | h640
            · linarith only [h619, h640, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h642 | h642
              · linarith only [h635, h642, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h644 | h644
                · linarith only [h1, h637, h644, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h646 | h646
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h647 | h647
                    · linarith only [h1, h2, h640, h644, h647, hc12, hc23, hlam, hphi]
                    · linarith only [h619, h647, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h1, h2, h619, h639, h646, hlam, hphi, u0ehi6, u0elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h651 | h651
            · linarith only [h619, h651, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h653 | h653
              · linarith only [h1, h2, h639, h651, h653, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h655 | h655
                · linarith only [h1, h2, h639, h655, hc34, hc45, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h657 | h657
                  · linarith only [h1, h2, h639, h651, h653, h657, hc12, hc24, hlam, hphi]
                  · linarith only [h1, h2, h619, h657, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]

end R2N4
