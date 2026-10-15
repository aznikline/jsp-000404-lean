import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_29S4
import Jsp000404.R1LeavesN7_29S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10236000 in
set_option maxHeartbeats 10236000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0 m hb0 hb2 hb3 hb5 h0

set_option maxHeartbeats 10236000 in
set_option maxHeartbeats 10236000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x1 m hb0 hb2 hb3 hb5 h0

set_option maxHeartbeats 5254000 in
set_option maxHeartbeats 5254000 in
theorem r1l7_21_15_M_LI_L_I_s1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
      · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h15, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h0, h12, h15, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h18, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h0, h12, h18, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h12, h13, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h12, h22, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                      · linarith only [h0, h12, h25, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h27 | h27
                        · linarith only [h0, h22, h27, h9, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
                          · linarith only [h0, h10, h29, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h2, h24, h29, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                      · linarith only [h0, h32, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                        · linarith only [h0, h12, h24, h34, h4, h6, h8, h9, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                          · linarith only [h0, h10, h12, h24, h36, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h38 | h38
                            · linarith only [h0, h12, h24, h38, h4, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h0, h12, h38, h4, h6, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h11, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
              · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                · linarith only [h10, h43, h9, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                  · linarith only [h0, h4, h43, h45, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                      · linarith only [h43, h48, h9, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h10, h4, h48, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h0, h10, h4, h47, h6, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h42, h5, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
            · linarith only [h0, h4, h53, h9, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h55 | h55
              · linarith only [h0, h4, h55, h9, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h63 | h63
                            · linarith only [h1, h57, h63, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                            · linarith only [h2, h59, h63, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h53, h59, h62, hlam]
                        · linarith only [h3, h53, h58, h59, h60, h61, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · linarith only [h0, h4, h6, h60, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                          · linarith only [h0, h4, h59, h69, h71, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h0, h4, h53, h6, h71, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h58, h70, h9, hlam]
                      · linarith only [h0, h4, h57, h59, h6, h69, h8, h9, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h4, h57, h58, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h77 | h77
                  · linarith only [h0, h4, h57, h6, h77, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h79 | h79
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h80 | h80
                      · linarith only [h0, h4, h57, h80, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h0, h4, h6, h80, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                      · linarith only [h0, h4, h57, h83, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h0, h4, h6, h83, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
          · rcases m.htr 1 2 4 (by decide) (by decide) with h87 | h87
            · rcases m.htr 1 2 5 (by decide) (by decide) with h88 | h88
              · rcases m.htr 1 3 4 (by decide) (by decide) with h89 | h89
                · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                    · linarith only [h2, h8, h91, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                      · linarith only [h0, h86, h93, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h89, h93, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h0, h4, h7, h89, h90, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h97 | h97
                  · linarith only [h0, h4, h6, h89, h97, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h99 | h99
                    · linarith only [h2, h8, h99, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                      · linarith only [h0, h101, h4, h89, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h103 | h103
                        · linarith only [h103, h86, h97, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h105 | h105
                          · linarith only [h0, h105, h6, h8, h86, h87, h89, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                            · linarith only [h107, h6, h8, hlam]
                            · rcases h1bigk with h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c | h109c
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h86, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p109_1, u1elo0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                rcases p109_3 (m.d 0 1) (by simp) with h112 | h112
                                · rcases p109_3 (m.d 1 2) (by simp) with h113 | h113
                                  · linarith only [h0, h113, hlam]
                                  · linarith only [h113, h86, hlam]
                                · linarith only [h112, hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                rcases p109_3 (m.d 0 1) (by simp) with h117 | h117
                                · rcases p109_3 (m.d 1 2) (by simp) with h118 | h118
                                  · linarith only [h0, h118, hlam]
                                  · linarith only [h118, h87, hlam]
                                · linarith only [h117, hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                rcases p109_3 (m.d 0 1) (by simp) with h122 | h122
                                · rcases p109_3 (m.d 1 2) (by simp) with h123 | h123
                                  · linarith only [h0, h123, hlam]
                                  · linarith only [h123, h88, hlam]
                                · linarith only [h122, hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h0, hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h0, h86, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p109_1, u1elo0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h0, h86, h89, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p109_1, u1elo0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h0, h86, h89, h99, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p109_1, u1elo0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h1, hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h86, hlam, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h89, hlam, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h97, hlam, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h2, hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h87, hlam, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h2, h86, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p109_1, u1elo0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h99, hlam, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h3, hlam, p109_0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h88, hlam, p109_1]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h1, h7, h86, h97, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p109_1, u1elo0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [h0, h4, h7, h97, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p109_1, u1elo0]
                              · have p109_0 := h109c.1
                                have p109_1 := h109c.2.1
                                have p109_2 := h109c.2.2.1
                                have p109_3 := h109c.2.2.2
                                linarith only [hlam, p109_0]
              · linarith only [h0, h5, h86, h88, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h148 | h148
              · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                · linarith only [h149, h86, h87, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
                  · linarith only [h0, h149, h151, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h153 | h153
                    · linarith only [h149, h153, h6, h8, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h148, h153, h87, hlam]
              · linarith only [h0, h148, h5, h86, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
            · linarith only [h0, h157, h4, h86, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
              · linarith only [h0, h159, h4, h86, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                    · linarith only [h1, h159, h161, h163, h5, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
                          · linarith only [h0, h165, h167, h4, h8, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h169 | h169
                            · linarith only [h0, h167, h169, h4, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                            · rcases h1bigk with h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                rcases p171_3 (m.d 0 1) (by simp) with h173 | h173
                                · rcases p171_3 (m.d 1 2) (by simp) with h174 | h174
                                  · linarith only [h174, hlam, p171_0]
                                  · rcases p171_3 (m.d 1 3) (by simp) with h176 | h176
                                    · linarith only [h1, h176, hlam]
                                    · linarith only [h176, h86, hlam]
                                · linarith only [h173, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h162, h169, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p171_1, u1elo0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                rcases p171_3 (m.d 0 1) (by simp) with h181 | h181
                                · rcases p171_3 (m.d 1 2) (by simp) with h182 | h182
                                  · linarith only [h0, h182, hlam]
                                  · rcases p171_3 (m.d 1 3) (by simp) with h184 | h184
                                    · linarith only [h1, h184, hlam]
                                    · linarith only [h161, h184, hlam]
                                · linarith only [h181, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                rcases p171_3 (m.d 0 1) (by simp) with h188 | h188
                                · rcases p171_3 (m.d 1 2) (by simp) with h189 | h189
                                  · linarith only [h0, h189, hlam]
                                  · rcases p171_3 (m.d 1 3) (by simp) with h191 | h191
                                    · linarith only [h1, h191, hlam]
                                    · linarith only [h162, h191, hlam]
                                · linarith only [h188, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h0, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h86, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h157, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h159, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h1, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h0, h157, h4, h86, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h0, h4, h86, hc15, hlam, hphi, ht01, ht0b, ht5b, p171_1, u1elo0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h2, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h161, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h163, hlam, p171_1]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h3, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h162, hlam, p171_0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p171_1, u1elo0]
                              · have p171_0 := h171c.1
                                have p171_1 := h171c.2.1
                                have p171_2 := h171c.2.2.1
                                have p171_3 := h171c.2.2.2
                                linarith only [hlam, p171_0]
                        · linarith only [h0, h166, h4, h7, h86, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h0, h162, h165, h4, h6, h86, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h0, h161, h162, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h218 | h218
                  · linarith only [h0, h161, h218, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h220 | h220
                    · linarith only [h161, h220, h6, h8, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h222 | h222
                      · linarith only [h0, h161, h222, h4, h86, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h222, h6, h8, h86, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h225 | h225
        · linarith only [h225, h6, h7, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h227 | h227
          · rcases m.htr 1 2 4 (by decide) (by decide) with h228 | h228
            · rcases m.htr 1 2 5 (by decide) (by decide) with h229 | h229
              · rcases m.htr 1 3 4 (by decide) (by decide) with h230 | h230
                · rcases m.htr 1 3 5 (by decide) (by decide) with h231 | h231
                  · linarith only [h0, h227, h231, h7, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h233 | h233
                    · linarith only [h1, h225, h230, h233, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                      · linarith only [h0, h227, h235, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h235, h6, h7, hc23, hc35, hlam, hphi]
                · linarith only [h230, h6, h7, hc13, hc35, hlam, hphi]
              · linarith only [h0, h227, h229, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h240 | h240
              · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
                · linarith only [h227, h228, h241, hlam]
                · linarith only [h241, h6, h7, hc13, hc35, hlam, hphi]
              · linarith only [h0, h227, h240, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h245 | h245
            · linarith only [h0, h227, h245, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h247 | h247
              · linarith only [h0, h227, h247, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h249 | h249
                · rcases m.htr 1 3 5 (by decide) (by decide) with h250 | h250
                  · linarith only [h1, h250, h7, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h252 | h252
                    · linarith only [h2, h225, h252, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h255 | h255
                        · linarith only [h255, h4, h7, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h257 | h257
                          · linarith only [h0, h225, h254, h255, h257, h5, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h259 | h259
                            · linarith only [h249, h257, h259, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · rcases h1bigk with h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                rcases p261_3 (m.d 0 1) (by simp) with h263 | h263
                                · rcases p261_3 (m.d 1 2) (by simp) with h264 | h264
                                  · linarith only [h264, hlam, p261_0]
                                  · rcases p261_3 (m.d 1 3) (by simp) with h266 | h266
                                    · linarith only [h1, h266, hlam]
                                    · linarith only [h227, h266, hlam]
                                · linarith only [h263, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h249, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p261_1, u1elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                rcases p261_3 (m.d 0 1) (by simp) with h271 | h271
                                · rcases p261_3 (m.d 1 2) (by simp) with h272 | h272
                                  · linarith only [h0, h272, hlam]
                                  · rcases p261_3 (m.d 1 3) (by simp) with h274 | h274
                                    · linarith only [h1, h274, hlam]
                                    · linarith only [h249, h274, hlam]
                                · linarith only [h271, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h249, h250, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p261_1, u1elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h0, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h227, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h245, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h247, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h1, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p261_1, u1elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h0, h227, h245, h255, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p261_1, u1elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h250, hlam, p261_1]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h2, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p261_1, u1elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h249, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h252, hlam, p261_1]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h3, hlam, p261_0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p261_1, u1elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h0, h247, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p261_1, u1elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [h0, h245, h247, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p261_1, u1elo0]
                              · have p261_0 := h261c.1
                                have p261_1 := h261c.2.1
                                have p261_2 := h261c.2.2.1
                                have p261_3 := h261c.2.2.2
                                linarith only [hlam, p261_0]
                      · linarith only [h1, h249, h254, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h249, h6, h7, hc13, hc35, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h301 | h301
      · rcases m.htr 0 4 5 (by decide) (by decide) with h302 | h302
        · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
          · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
            · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
              · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                · linarith only [h301, h306, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h308 | h308
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h309 | h309
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h310 | h310
                      · linarith only [h0, h1, h308, h310, h4, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h312 | h312
                        · linarith only [h0, h304, h310, h312, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h1, h308, h312, h6, hc23, hc34, hlam, hphi]
                    · linarith only [h2, h302, h306, h308, h309, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h301, h308, h6, hc13, hc34, hlam, hphi]
              · linarith only [h0, h303, h305, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h318 | h318
              · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                · linarith only [h301, h319, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h321 | h321
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h322 | h322
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h323 | h323
                      · linarith only [h0, h303, h323, h6, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h325 | h325
                        · linarith only [h0, h303, h325, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h1, h321, h325, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h2, h302, h304, h318, h322, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h301, h321, h6, hc13, hc34, hlam, hphi]
              · linarith only [h0, h303, h318, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
            · linarith only [h0, h303, h331, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h333 | h333
              · linarith only [h0, h303, h333, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h335 | h335
                · linarith only [h301, h335, h6, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h337 | h337
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h338 | h338
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h339 | h339
                      · linarith only [h0, h301, h333, h339, h4, h5, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h341 | h341
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h342 | h342
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h343 | h343
                            · rcases h1bigk with h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                rcases p344_3 (m.d 0 1) (by simp) with h346 | h346
                                · rcases p344_3 (m.d 1 2) (by simp) with h347 | h347
                                  · linarith only [h347, hlam, p344_0]
                                  · rcases p344_3 (m.d 1 3) (by simp) with h349 | h349
                                    · linarith only [h1, h349, hlam]
                                    · linarith only [h303, h349, hlam]
                                · linarith only [h346, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h337, h343, hc45, hlam, hphi, ht01, ht0b, ht5b, p344_1, u1elo0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h335, h337, h343, hc45, hlam, hphi, ht01, ht0b, ht5b, p344_1, u1elo0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                rcases p344_3 (m.d 0 1) (by simp) with h355 | h355
                                · rcases p344_3 (m.d 1 2) (by simp) with h356 | h356
                                  · linarith only [h0, h356, hlam]
                                  · rcases p344_3 (m.d 1 3) (by simp) with h358 | h358
                                    · linarith only [h1, h358, hlam]
                                    · linarith only [h337, h358, hlam]
                                · linarith only [h355, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h0, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h303, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h331, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h333, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h1, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p344_1, u1elo0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h335, hlam, p344_1]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht5b, p344_1, u1elo0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h2, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p344_1, u1elo0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p344_1, u1elo0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h2, h333, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p344_1, u1elo0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h3, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p344_1, u1elo0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h337, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [h338, hlam, p344_0]
                              · have p344_0 := h344c.1
                                have p344_1 := h344c.2.1
                                have p344_2 := h344c.2.2.1
                                have p344_3 := h344c.2.2.2
                                linarith only [hlam, p344_0]
                            · linarith only [h2, h302, h343, h6, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h3, h331, h338, h342, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h1, h337, h341, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h2, h302, h335, h337, h338, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h301, h337, h6, hc13, hc34, hlam, hphi]
        · linarith only [h301, h302, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h388 | h388
        · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
          · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
            · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
              · rcases m.htr 1 3 4 (by decide) (by decide) with h392 | h392
                · linarith only [h1, h392, h6, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h394 | h394
                  · linarith only [h1, h301, h394, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h396 | h396
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
                      · linarith only [h389, h397, h6, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h399 | h399
                        · linarith only [h1, h301, h389, h399, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h401 | h401
                          · linarith only [h0, h390, h401, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h0, h390, h396, h401, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                      · linarith only [h1, h388, h389, h396, h404, h6, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h406 | h406
                        · linarith only [h301, h388, h389, h392, h396, h406, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h408 | h408
                          · linarith only [h0, h389, h390, h392, h396, h408, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h410 | h410
                            · rcases h1bigk with h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h389, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p411_1, u1elo0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                rcases p411_3 (m.d 0 1) (by simp) with h414 | h414
                                · rcases p411_3 (m.d 1 2) (by simp) with h415 | h415
                                  · linarith only [h0, h415, hlam]
                                  · linarith only [h389, h415, hlam]
                                · linarith only [h414, hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                rcases p411_3 (m.d 0 1) (by simp) with h419 | h419
                                · rcases p411_3 (m.d 1 2) (by simp) with h420 | h420
                                  · linarith only [h0, h420, hlam]
                                  · linarith only [h390, h420, hlam]
                                · linarith only [h419, hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                rcases p411_3 (m.d 0 1) (by simp) with h424 | h424
                                · rcases p411_3 (m.d 1 2) (by simp) with h425 | h425
                                  · linarith only [h0, h425, hlam]
                                  · linarith only [h391, h425, hlam]
                                · linarith only [h424, hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h0, hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h0, h389, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p411_1, u1elo0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h0, h389, h392, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p411_1, u1elo0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h0, h389, h392, h396, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p411_1, u1elo0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h1, hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h389, hlam, p411_1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h392, hlam, p411_1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h394, hlam, p411_1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h2, hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h390, hlam, p411_1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h388, h389, h396, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p411_1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h396, hlam, p411_1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h3, hlam, p411_0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h391, hlam, p411_1]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h3, h389, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p411_1, u1elo0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [h2, h388, h390, h396, h404, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p411_1, u1elo0]
                              · have p411_0 := h411c.1
                                have p411_1 := h411c.2.1
                                have p411_2 := h411c.2.2.1
                                have p411_3 := h411c.2.2.2
                                linarith only [hlam, p411_0]
                            · linarith only [h1, h2, h388, h389, h410, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h389, h391, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h451 | h451
              · rcases m.htr 1 3 4 (by decide) (by decide) with h452 | h452
                · linarith only [h1, h388, h452, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h454 | h454
                  · linarith only [h1, h301, h454, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h456 | h456
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h457 | h457
                      · linarith only [h0, h4, h457, h6, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h459 | h459
                        · linarith only [h1, h301, h389, h459, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h461 | h461
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h462 | h462
                            · rcases h1bigk with h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h389, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p463_1, u1elo0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                rcases p463_3 (m.d 0 1) (by simp) with h466 | h466
                                · rcases p463_3 (m.d 1 2) (by simp) with h467 | h467
                                  · linarith only [h0, h467, hlam]
                                  · linarith only [h389, h467, hlam]
                                · linarith only [h466, hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h390, h451, h459, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p463_1, u1elo0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                rcases p463_3 (m.d 0 1) (by simp) with h472 | h472
                                · rcases p463_3 (m.d 1 2) (by simp) with h473 | h473
                                  · linarith only [h0, h473, hlam]
                                  · linarith only [h451, h473, hlam]
                                · linarith only [h472, hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h0, hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h389, h390, h457, hc23, hc34, hlam, hphi, p463_1]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h390, hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h2, h390, hc15, hlam, hphi, ht01, ht0b, ht5b, p463_1, u1elo0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h1, hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h389, hlam, p463_1]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h452, hlam, p463_1]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h454, hlam, p463_1]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h2, hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p463_1, u1elo0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h2, h389, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p463_1, u1elo0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h2, h451, h459, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p463_1, u1elo0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h3, hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h451, hlam, p463_1]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h3, h389, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p463_1, u1elo0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [h456, hlam, p463_0]
                              · have p463_0 := h463c.1
                                have p463_1 := h463c.2.1
                                have p463_2 := h463c.2.2.1
                                have p463_3 := h463c.2.2.2
                                linarith only [hlam, p463_0]
                            · linarith only [h1, h2, h388, h389, h462, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h390, h451, h456, h459, h461, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · linarith only [h2, h388, h390, h451, h456, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h0, h389, h451, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h501 | h501
            · linarith only [h0, h389, h4, h501, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h503 | h503
              · linarith only [h0, h389, h4, h503, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h505 | h505
                · linarith only [h0, h389, h4, h505, h6, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h507 | h507
                  · linarith only [h301, h389, h4, h507, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h509 | h509
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h510 | h510
                      · linarith only [h4, h510, h6, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h512 | h512
                        · linarith only [h301, h4, h512, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h514 | h514
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h515 | h515
                            · rcases h1bigk with h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                rcases p516_3 (m.d 0 1) (by simp) with h518 | h518
                                · rcases p516_3 (m.d 1 2) (by simp) with h519 | h519
                                  · linarith only [h519, hlam, p516_0]
                                  · rcases p516_3 (m.d 1 3) (by simp) with h521 | h521
                                    · linarith only [h1, h521, hlam]
                                    · linarith only [h389, h521, hlam]
                                · linarith only [h518, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                rcases p516_3 (m.d 0 1) (by simp) with h525 | h525
                                · rcases p516_3 (m.d 1 2) (by simp) with h526 | h526
                                  · linarith only [h0, h526, hlam]
                                  · rcases p516_3 (m.d 1 3) (by simp) with h528 | h528
                                    · linarith only [h528, hlam, p516_0]
                                    · rcases p516_3 (m.d 1 4) (by simp) with h530 | h530
                                      · linarith only [h2, h530, hlam]
                                      · linarith only [h505, h530, hlam]
                                · linarith only [h525, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h509, hc45, hlam, hphi, ht01, ht0b, ht5b, p516_1, u1elo0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                rcases p516_3 (m.d 0 1) (by simp) with h535 | h535
                                · rcases p516_3 (m.d 1 2) (by simp) with h536 | h536
                                  · linarith only [h0, h536, hlam]
                                  · rcases p516_3 (m.d 1 3) (by simp) with h538 | h538
                                    · linarith only [h1, h538, hlam]
                                    · rcases p516_3 (m.d 1 4) (by simp) with h540 | h540
                                      · linarith only [h2, h540, hlam]
                                      · linarith only [h509, h540, hlam]
                                · linarith only [h535, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h0, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h389, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h501, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h503, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h1, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p516_1, u1elo0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h505, hlam, p516_1]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h507, hlam, p516_1]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h2, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p516_1, u1elo0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p516_1, u1elo0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h2, h389, h507, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p516_1, u1elo0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h3, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p516_1, u1elo0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h0, h389, h5, h503, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p516_1, u1elo0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [h509, hlam, p516_0]
                              · have p516_0 := h516c.1
                                have p516_1 := h516c.2.1
                                have p516_2 := h516c.2.2.1
                                have p516_3 := h516c.2.2.2
                                linarith only [hlam, p516_0]
                            · linarith only [h388, h515, h6, hlam]
                          · linarith only [h501, h509, h514, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h566 | h566
                      · linarith only [h1, h388, h4, h509, h566, h6, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h568 | h568
                        · linarith only [h0, h301, h4, h568, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h570 | h570
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h571 | h571
                            · rcases h1bigk with h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c | h572c
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                rcases p572_3 (m.d 0 1) (by simp) with h574 | h574
                                · rcases p572_3 (m.d 1 2) (by simp) with h575 | h575
                                  · linarith only [h575, hlam, p572_0]
                                  · rcases p572_3 (m.d 1 3) (by simp) with h577 | h577
                                    · linarith only [h1, h577, hlam]
                                    · linarith only [h389, h577, hlam]
                                · linarith only [h574, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                rcases p572_3 (m.d 0 1) (by simp) with h581 | h581
                                · rcases p572_3 (m.d 1 2) (by simp) with h582 | h582
                                  · linarith only [h0, h582, hlam]
                                  · rcases p572_3 (m.d 1 3) (by simp) with h584 | h584
                                    · linarith only [h584, hlam, p572_0]
                                    · rcases p572_3 (m.d 1 4) (by simp) with h586 | h586
                                      · linarith only [h2, h586, hlam]
                                      · linarith only [h505, h586, hlam]
                                · linarith only [h581, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                rcases p572_3 (m.d 0 1) (by simp) with h590 | h590
                                · rcases p572_3 (m.d 1 2) (by simp) with h591 | h591
                                  · linarith only [h0, h591, hlam]
                                  · rcases p572_3 (m.d 1 3) (by simp) with h593 | h593
                                    · linarith only [h1, h593, hlam]
                                    · rcases p572_3 (m.d 1 4) (by simp) with h595 | h595
                                      · linarith only [h595, hlam, p572_0]
                                      · rcases p572_3 (m.d 1 5) (by simp) with h597 | h597
                                        · linarith only [h3, h597, hlam]
                                        · linarith only [h509, h597, hlam]
                                · linarith only [h590, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                rcases p572_3 (m.d 0 1) (by simp) with h601 | h601
                                · rcases p572_3 (m.d 1 2) (by simp) with h602 | h602
                                  · linarith only [h0, h602, hlam]
                                  · rcases p572_3 (m.d 1 3) (by simp) with h604 | h604
                                    · linarith only [h1, h604, hlam]
                                    · rcases p572_3 (m.d 1 4) (by simp) with h606 | h606
                                      · linarith only [h2, h606, hlam]
                                      · rcases p572_3 (m.d 1 5) (by simp) with h608 | h608
                                        · linarith only [h608, hlam, p572_0]
                                        · rcases h5bigk with h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c | h610c
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [hlam, p610_0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            rcases p610_3 (m.d 0 5) (by simp) with h612 | h612
                                            · rcases p610_3 (m.d 1 5) (by simp) with h613 | h613
                                              · linarith only [h3, h613, hlam]
                                              · rcases p610_3 (m.d 2 5) (by simp) with h615 | h615
                                                · linarith only [h5, h615, hlam]
                                                · linarith only [h503, h615, hlam]
                                            · linarith only [h3, h612, hlam]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h301, h503, hc12, hc35, hlam, hphi, ht23, p610_1]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h301, hlam, p610_1]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h2, h388, h389, h505, h509, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p610_1, u1elo0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h3, hlam, p610_0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [hlam, p610_0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h503, hlam, p610_0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h507, hlam, p610_1]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h509, hlam, p610_1]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h5, hlam, p610_1]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h0, h389, h5, h505, h509, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p610_1, u1elo0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [hlam, p610_0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h568, hlam, p610_1]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h0, h389, h5, h505, h509, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p610_1, u1elo0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h301, h389, h4, hc12, hc35, hlam, hphi, ht23, p610_1]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            rcases p610_3 (m.d 0 5) (by simp) with h633 | h633
                                            · linarith only [h301, h633, hlam]
                                            · linarith only [h3, h633, hlam]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h389, h505, h509, h570, h571, hc12, hc34, hlam, hphi, ht23, p610_1]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [hlam, p610_0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h389, h505, h509, h571, hc12, hc34, hlam, hphi, ht23, p610_1]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h388, hlam, p610_0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h389, h505, h509, h570, hc12, hc24, hlam, hphi, p610_1]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h570, hlam, p610_0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [h571, hlam, p610_0]
                                          · have p610_0 := h610c.1
                                            have p610_1 := h610c.2.1
                                            have p610_2 := h610c.2.2.1
                                            have p610_3 := h610c.2.2.2
                                            linarith only [hlam, p610_0]
                                · linarith only [h601, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h0, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h389, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h501, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h503, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h1, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p572_1, u1elo0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h505, hlam, p572_1]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h507, hlam, p572_1]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h2, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h3, h509, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p572_1, u1elo0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h3, h509, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p572_1, u1elo0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h509, hlam, p572_1]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h3, hlam, p572_0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h0, h5, h503, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p572_1, u1elo0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h0, h389, h5, h503, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p572_1, u1elo0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [h0, h5, h503, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p572_1, u1elo0]
                              · have p572_0 := h572c.1
                                have p572_1 := h572c.2.1
                                have p572_2 := h572c.2.2.1
                                have p572_3 := h572c.2.2.2
                                linarith only [hlam, p572_0]
                            · linarith only [h0, h389, h4, h5, h570, h571, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                          · linarith only [h388, h501, h570, h6, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h667 | h667
          · rcases m.htr 1 2 4 (by decide) (by decide) with h668 | h668
            · rcases m.htr 1 2 5 (by decide) (by decide) with h669 | h669
              · rcases m.htr 1 3 4 (by decide) (by decide) with h670 | h670
                · linarith only [h1, h6, h670, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h672 | h672
                  · linarith only [h1, h301, h672, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h674 | h674
                    · linarith only [h2, h388, h674, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h676 | h676
                      · linarith only [h0, h6, h667, h676, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h678 | h678
                        · linarith only [h1, h301, h667, h678, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h680 | h680
                          · linarith only [h0, h388, h6, h668, h680, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h682 | h682
                            · rcases h1bigk with h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c | h683c
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [hlam, p683_0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h667, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p683_1, u1elo0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                rcases p683_3 (m.d 0 1) (by simp) with h686 | h686
                                · rcases p683_3 (m.d 1 2) (by simp) with h687 | h687
                                  · linarith only [h0, h687, hlam]
                                  · linarith only [h667, h687, hlam]
                                · linarith only [h686, hlam, p683_0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                rcases p683_3 (m.d 0 1) (by simp) with h691 | h691
                                · rcases p683_3 (m.d 1 2) (by simp) with h692 | h692
                                  · linarith only [h0, h692, hlam]
                                  · linarith only [h668, h692, hlam]
                                · linarith only [h691, hlam, p683_0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                rcases p683_3 (m.d 0 1) (by simp) with h696 | h696
                                · rcases p683_3 (m.d 1 2) (by simp) with h697 | h697
                                  · linarith only [h0, h697, hlam]
                                  · linarith only [h669, h697, hlam]
                                · linarith only [h696, hlam, p683_0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h0, hlam, p683_0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [hlam, p683_0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h0, h667, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p683_1, u1elo0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h0, h667, h670, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p683_1, u1elo0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h0, h667, h670, h674, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p683_1, u1elo0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h1, hlam, p683_0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h667, hlam, p683_1]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [hlam, p683_0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h670, hlam, p683_1]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h672, hlam, p683_1]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h2, hlam, p683_0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h668, hlam, p683_1]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h2, h667, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p683_1, u1elo0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [hlam, p683_0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h674, hlam, p683_1]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h3, hlam, p683_0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h669, hlam, p683_1]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h3, h667, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p683_1, u1elo0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [h0, h669, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p683_1, u1elo0]
                              · have p683_0 := h683c.1
                                have p683_1 := h683c.2.1
                                have p683_2 := h683c.2.2.1
                                have p683_3 := h683c.2.2.2
                                linarith only [hlam, p683_0]
                            · rcases h1bigk with h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c | h721c
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [hlam, p721_0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h667, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p721_1, u1elo0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                rcases p721_3 (m.d 0 1) (by simp) with h724 | h724
                                · rcases p721_3 (m.d 1 2) (by simp) with h725 | h725
                                  · linarith only [h0, h725, hlam]
                                  · linarith only [h667, h725, hlam]
                                · linarith only [h724, hlam, p721_0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                rcases p721_3 (m.d 0 1) (by simp) with h729 | h729
                                · rcases p721_3 (m.d 1 2) (by simp) with h730 | h730
                                  · linarith only [h0, h730, hlam]
                                  · linarith only [h668, h730, hlam]
                                · linarith only [h729, hlam, p721_0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                rcases p721_3 (m.d 0 1) (by simp) with h734 | h734
                                · rcases p721_3 (m.d 1 2) (by simp) with h735 | h735
                                  · linarith only [h0, h735, hlam]
                                  · linarith only [h669, h735, hlam]
                                · linarith only [h734, hlam, p721_0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h0, hlam, p721_0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [hlam, p721_0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h0, h667, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p721_1, u1elo0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h0, h668, h676, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p721_1, u1elo0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p721_1, u1elo0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h1, hlam, p721_0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h667, hlam, p721_1]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [hlam, p721_0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h670, hlam, p721_1]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h672, hlam, p721_1]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h2, hlam, p721_0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h668, hlam, p721_1]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h2, h667, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p721_1, u1elo0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [hlam, p721_0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h674, hlam, p721_1]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h3, hlam, p721_0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h669, hlam, p721_1]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h3, h667, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p721_1, u1elo0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p721_1, u1elo0]
                              · have p721_0 := h721c.1
                                have p721_1 := h721c.2.1
                                have p721_2 := h721c.2.2.1
                                have p721_3 := h721c.2.2.2
                                linarith only [hlam, p721_0]
              · linarith only [h0, h5, h667, h669, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h760 | h760
              · rcases m.htr 1 3 4 (by decide) (by decide) with h761 | h761
                · linarith only [h1, h2, h6, h667, h668, h761, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h763 | h763
                  · linarith only [h2, h301, h388, h667, h668, h763, hc03, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h765 | h765
                    · linarith only [h2, h388, h765, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h668, h760, h765, hlam]
              · linarith only [h0, h5, h667, h760, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h769 | h769
            · linarith only [h0, h4, h667, h769, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h771 | h771
              · linarith only [h0, h4, h667, h771, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h773 | h773
                · linarith only [h4, h6, h667, h773, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h775 | h775
                  · linarith only [h301, h4, h667, h775, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h777 | h777
                    · linarith only [h2, h388, h777, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h779 | h779
                      · linarith only [h4, h6, h779, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h781 | h781
                        · linarith only [h301, h4, h781, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h783 | h783
                          · linarith only [h388, h4, h6, h667, h783, hc12, hc24, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h785 | h785
                            · linarith only [h388, h4, h6, h667, h785, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h4, h6, h667, h785, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h788 | h788
    · rcases m.htr 0 3 5 (by decide) (by decide) with h789 | h789
      · linarith only [h4, h5, h789, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h791 | h791
        · linarith only [h4, h5, h788, h791, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h793 | h793
          · rcases m.htr 1 2 4 (by decide) (by decide) with h794 | h794
            · rcases m.htr 1 2 5 (by decide) (by decide) with h795 | h795
              · linarith only [h4, h5, h788, h795, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h797 | h797
                · rcases m.htr 1 3 5 (by decide) (by decide) with h798 | h798
                  · linarith only [h1, h789, h798, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h800 | h800
                    · linarith only [h2, h791, h800, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h802 | h802
                      · linarith only [h3, h793, h795, h802, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h789, h797, h802, hc23, hc35, hlam, hphi]
                · linarith only [h788, h789, h797, hc13, hc35, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h806 | h806
              · linarith only [h5, h794, h806, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h808 | h808
                · linarith only [h793, h794, h808, hlam]
                · linarith only [h788, h789, h808, hc13, hc35, hlam, hphi]
          · linarith only [h4, h5, h793, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h812 | h812
      · linarith only [h4, h5, h812, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h814 | h814
        · rcases m.htr 1 2 3 (by decide) (by decide) with h815 | h815
          · rcases m.htr 1 2 4 (by decide) (by decide) with h816 | h816
            · rcases m.htr 1 2 5 (by decide) (by decide) with h817 | h817
              · linarith only [h0, h5, h817, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h819 | h819
                · linarith only [h1, h788, h819, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h821 | h821
                  · linarith only [h0, h812, h816, h819, h821, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h823 | h823
                    · linarith only [h816, h817, h823, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h825 | h825
                      · linarith only [h1, h788, h815, h825, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h827 | h827
                        · linarith only [h812, h814, h816, h817, h823, h825, h827, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h829 | h829
                          · linarith only [h816, h817, h823, h829, hlam]
                          · linarith only [h0, h2, h5, h814, h816, h825, h829, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h832 | h832
              · linarith only [h0, h5, h832, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h834 | h834
                · linarith only [h1, h788, h814, h834, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h836 | h836
                  · linarith only [h1, h812, h836, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h838 | h838
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h839 | h839
                      · linarith only [h788, h815, h839, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h841 | h841
                        · linarith only [h4, h5, h812, h841, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h843 | h843
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h844 | h844
                            · rcases h1bigk with h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h815, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p845_1, u1elo0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                rcases p845_3 (m.d 0 1) (by simp) with h848 | h848
                                · rcases p845_3 (m.d 1 2) (by simp) with h849 | h849
                                  · linarith only [h0, h849, hlam]
                                  · linarith only [h815, h849, hlam]
                                · linarith only [h848, hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h838, hc45, hlam, hphi, ht01, ht0b, ht5b, p845_1, u1elo0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h815, h832, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p845_1, u1elo0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h0, hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h0, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p845_1, u1elo0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h816, hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h832, hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h1, hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h815, hlam, p845_1]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h834, hlam, p845_1]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h836, hlam, p845_1]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h2, hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p845_1, u1elo0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h2, h815, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p845_1, u1elo0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h2, hc15, hlam, hphi, ht01, ht0b, ht5b, p845_1, u1elo0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h3, hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h815, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p845_1, u1elo4]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h3, h815, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p845_1, u1elo0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [h838, hlam, p845_0]
                              · have p845_0 := h845c.1
                                have p845_1 := h845c.2.1
                                have p845_2 := h845c.2.2.1
                                have p845_3 := h845c.2.2.2
                                linarith only [hlam, p845_0]
                            · linarith only [h0, h5, h815, h839, h843, h844, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h2, h815, h816, h838, h843, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h2, h814, h815, h816, h838, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · linarith only [h4, h5, h815, hc12, hc25, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h879 | h879
          · rcases m.htr 1 2 4 (by decide) (by decide) with h880 | h880
            · rcases m.htr 1 2 5 (by decide) (by decide) with h881 | h881
              · linarith only [h0, h5, h881, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h883 | h883
                · linarith only [h1, h788, h883, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h885 | h885
                  · linarith only [h1, h4, h5, h812, h885, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h887 | h887
                    · linarith only [h3, h814, h880, h881, h887, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h889 | h889
                      · linarith only [h4, h5, h788, h889, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h891 | h891
                        · linarith only [h0, h5, h812, h880, h889, h891, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h893 | h893
                          · linarith only [h0, h5, h814, h880, h893, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h895 | h895
                            · linarith only [h0, h5, h880, h889, h893, h895, hc23, hc34, hlam, hphi]
                            · rcases h1bigk with h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c | h897c
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [hlam, p897_0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h880, h889, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p897_1, u1elo0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                rcases p897_3 (m.d 0 1) (by simp) with h900 | h900
                                · rcases p897_3 (m.d 1 2) (by simp) with h901 | h901
                                  · linarith only [h0, h901, hlam]
                                  · linarith only [h879, h901, hlam]
                                · linarith only [h900, hlam, p897_0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                rcases p897_3 (m.d 0 1) (by simp) with h905 | h905
                                · rcases p897_3 (m.d 1 2) (by simp) with h906 | h906
                                  · linarith only [h0, h906, hlam]
                                  · linarith only [h880, h906, hlam]
                                · linarith only [h905, hlam, p897_0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h880, h881, h889, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p897_1, u1elo0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h0, hlam, p897_0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [hlam, p897_0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h0, h5, h879, h891, hc23, hc35, hlam, hphi, p897_1]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h3, h879, h881, h883, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p897_1, u1elo0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h881, hlam, p897_0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h1, hlam, p897_0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h879, hlam, p897_1]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [hlam, p897_0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h883, hlam, p897_1]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h885, hlam, p897_1]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h2, hlam, p897_0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h880, hlam, p897_1]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h2, h879, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p897_1, u1elo0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [hlam, p897_0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h887, hlam, p897_1]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h3, hlam, p897_0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p897_1, u1elo0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h3, h879, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p897_1, u1elo0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p897_1, u1elo0]
                              · have p897_0 := h897c.1
                                have p897_1 := h897c.2.1
                                have p897_2 := h897c.2.2.1
                                have p897_3 := h897c.2.2.2
                                linarith only [hlam, p897_0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h931 | h931
              · linarith only [h5, h880, h931, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h933 | h933
                · linarith only [h1, h788, h933, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h935 | h935
                  · linarith only [h0, h812, h879, h935, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h937 | h937
                    · linarith only [h2, h814, h937, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h939 | h939
                      · linarith only [h2, h4, h5, h788, h880, h939, hc12, hc25, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h941 | h941
                        · linarith only [h3, h4, h5, h812, h941, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h943 | h943
                          · linarith only [h2, h814, h879, h880, h939, h943, hc23, hc34, hlam, hphi]
                          · linarith only [h879, h880, h943, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h4, h5, h879, hc12, hc25, hlam, hphi]

end R2N4
