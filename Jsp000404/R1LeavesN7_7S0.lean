import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
  · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
    · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
      · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
        · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
          · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
            · linarith only [h0, h10, h17, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · linarith only [h0, h10, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
            · linarith only [h0, h16, h20, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
              · linarith only [h0, h11, h22, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                · linarith only [h0, h10, h13, h16, h22, h24, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h10, h13, h15, h16, h24, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h27 | h27
          · rcases m.htr 2 3 5 (by decide) (by decide) with h28 | h28
            · linarith only [h0, h10, h28, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · linarith only [h1, h14, h27, h28, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
            · linarith only [h0, h27, h31, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
              · linarith only [h13, h15, h27, h33, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h35 | h35
                · linarith only [h13, h15, h35, hlam]
                · rcases h1bigk with h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c | h37c
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h12, hc01, hlam, hphi, ht0b, ht5b, p37_1, u5ehi2]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h13, h27, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    rcases p37_3 (m.d 0 1) (by simp) with h41 | h41
                    · rcases p37_3 (m.d 1 2) (by simp) with h42 | h42
                      · linarith only [h0, h42, hlam]
                      · linarith only [h11, h42, hlam]
                    · linarith only [h41, hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    rcases p37_3 (m.d 0 1) (by simp) with h46 | h46
                    · rcases p37_3 (m.d 1 2) (by simp) with h47 | h47
                      · linarith only [h0, h47, hlam]
                      · linarith only [h12, h47, hlam]
                    · linarith only [h46, hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h0, hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h14, h27, h35, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p37_1]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h0, h13, h27, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p37_1, u5ehi1]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h1, hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h10, hlam, p37_1]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h0, h10, h13, h27, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h0, h10, h12, hc01, hlam, hphi, ht0b, ht5b, p37_1, u5ehi2]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h2, hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h11, hlam, p37_1]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h13, hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h15, hlam, p37_1]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h3, hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h12, hlam, p37_1]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h14, hlam, p37_0]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [h13, h27, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p37_1]
                  · have p37_0 := h37c.1
                    have p37_1 := h37c.2.1
                    have p37_2 := h37c.2.2.1
                    have p37_3 := h37c.2.2.2
                    linarith only [hlam, p37_0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h71 | h71
        · linarith only [h0, h13, h14, h4, h71, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
          · rcases m.htr 2 3 5 (by decide) (by decide) with h74 | h74
            · linarith only [h0, h10, h14, h74, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
              · linarith only [h0, h11, h71, h76, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                · linarith only [h10, h11, h14, h71, h73, h78, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · rcases h1bigk with h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h12, hc01, hlam, hphi, ht0b, ht5b, p80_1, u5ehi2]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    rcases p80_3 (m.d 0 1) (by simp) with h83 | h83
                    · rcases p80_3 (m.d 1 2) (by simp) with h84 | h84
                      · linarith only [h0, h84, hlam]
                      · linarith only [h10, h84, hlam]
                    · linarith only [h83, hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    rcases p80_3 (m.d 0 1) (by simp) with h88 | h88
                    · rcases p80_3 (m.d 1 2) (by simp) with h89 | h89
                      · linarith only [h0, h89, hlam]
                      · linarith only [h11, h89, hlam]
                    · linarith only [h88, hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    rcases p80_3 (m.d 0 1) (by simp) with h93 | h93
                    · rcases p80_3 (m.d 1 2) (by simp) with h94 | h94
                      · linarith only [h0, h94, hlam]
                      · linarith only [h12, h94, hlam]
                    · linarith only [h93, hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h0, hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h0, h10, h73, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p80_1]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    rcases p80_3 (m.d 0 1) (by simp) with h101 | h101
                    · rcases p80_3 (m.d 1 2) (by simp) with h102 | h102
                      · rcases p80_3 (m.d 1 3) (by simp) with h103 | h103
                        · linarith only [h10, h103, hlam]
                        · linarith only [h103, h13, hlam]
                      · linarith only [h102, h11, hlam]
                    · linarith only [h101, h2, hlam]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h0, h12, h73, h74, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p80_1]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h1, hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h10, hlam, p80_1]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h0, h14, h4, h7, h78, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p80_1]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h14, hlam, p80_1]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h2, hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h11, hlam, p80_1]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h13, hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h71, hlam, p80_1]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h3, hlam, p80_0]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h12, hlam, p80_1]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [h10, h3, h73, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p80_1]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    rcases p80_3 (m.d 0 1) (by simp) with h122 | h122
                    · rcases p80_3 (m.d 1 2) (by simp) with h123 | h123
                      · rcases p80_3 (m.d 1 3) (by simp) with h124 | h124
                        · linarith only [h124, h14, hlam]
                        · linarith only [h124, h13, hlam]
                      · linarith only [h11, h123, hlam]
                    · linarith only [h122, h2, hlam]
                  · have p80_0 := h80c.1
                    have p80_1 := h80c.2.1
                    have p80_2 := h80c.2.2.1
                    have p80_3 := h80c.2.2.2
                    linarith only [hlam, p80_0]
          · linarith only [h0, h13, h14, h4, h73, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h131 | h131
      · linarith only [h0, h13, h131, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h133 | h133
        · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
          · linarith only [h0, h10, h13, h134, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h136 | h136
            · linarith only [h0, h10, h131, h136, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h138 | h138
              · linarith only [h0, h11, h138, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h140 | h140
                · rcases h1bigk with h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c | h141c
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [hlam, p141_0]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h11, h133, h134, h138, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    rcases p141_3 (m.d 0 1) (by simp) with h144 | h144
                    · rcases p141_3 (m.d 1 2) (by simp) with h145 | h145
                      · linarith only [h0, h145, hlam]
                      · linarith only [h10, h145, hlam]
                    · linarith only [h144, hlam, p141_0]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h133, h134, h138, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    rcases p141_3 (m.d 0 1) (by simp) with h150 | h150
                    · rcases p141_3 (m.d 1 2) (by simp) with h151 | h151
                      · linarith only [h0, h151, hlam]
                      · linarith only [h12, h151, hlam]
                    · linarith only [h150, hlam, p141_0]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h0, hlam, p141_0]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [hlam, p141_0]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    rcases p141_3 (m.d 0 1) (by simp) with h157 | h157
                    · rcases p141_3 (m.d 1 2) (by simp) with h158 | h158
                      · rcases p141_3 (m.d 1 3) (by simp) with h159 | h159
                        · linarith only [h10, h159, hlam]
                        · rcases p141_3 (m.d 1 4) (by simp) with h161 | h161
                          · linarith only [h11, h161, hlam]
                          · linarith only [h13, h161, hlam]
                      · linarith only [h10, h158, hlam]
                    · linarith only [h1, h157, hlam]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h0, h133, h134, h138, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h0, h133, h134, h138, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h1, hlam, p141_0]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h10, hlam, p141_1]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [hlam, p141_0]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h13, hlam, p141_1]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h131, hlam, p141_1]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h2, hlam, p141_0]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h11, hlam, p141_1]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    rcases p141_3 (m.d 0 1) (by simp) with h175 | h175
                    · rcases p141_3 (m.d 1 2) (by simp) with h176 | h176
                      · rcases p141_3 (m.d 1 3) (by simp) with h177 | h177
                        · linarith only [h13, h177, hlam]
                        · rcases p141_3 (m.d 1 4) (by simp) with h179 | h179
                          · rcases p141_3 (m.d 1 5) (by simp) with h180 | h180
                            · linarith only [h133, h180, hlam]
                            · linarith only [h131, h180, hlam]
                          · linarith only [h13, h179, hlam]
                      · linarith only [h10, h176, hlam]
                    · linarith only [h1, h175, hlam]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [hlam, p141_0]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h133, h134, h138, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h3, hlam, p141_0]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h12, hlam, p141_1]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    rcases p141_3 (m.d 0 1) (by simp) with h190 | h190
                    · rcases p141_3 (m.d 1 2) (by simp) with h191 | h191
                      · rcases p141_3 (m.d 1 3) (by simp) with h192 | h192
                        · linarith only [h131, h192, hlam]
                        · rcases p141_3 (m.d 1 4) (by simp) with h194 | h194
                          · rcases p141_3 (m.d 1 5) (by simp) with h195 | h195
                            · rcases h1emax with h196 | h196 | h196 | h196 | h196
                              · linarith only [h0, h131, h140, h196, h4, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p141_1]
                              · linarith only [h12, h196, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                              · rcases h3bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h131, h140, h7, hlam, p141_1, p199_2]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h10, h131, h140, h7, hlam, p141_1, p199_2]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h0, h10, h131, h140, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1, p199_1]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h0, h10, h131, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1, p199_1]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h1, hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h11, h133, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p141_1, p199_1]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h13, hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h131, hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h4, hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h10, hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h134, hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h136, hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h7, hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  rcases p199_3 (m.d 0 3) (by simp) with h216 | h216
                                  · rcases p199_3 (m.d 1 3) (by simp) with h217 | h217
                                    · linarith only [h217, hlam, p199_0]
                                    · rcases p199_3 (m.d 2 3) (by simp) with h219 | h219
                                      · linarith only [h134, h219, hlam]
                                      · rcases p199_3 (m.d 3 4) (by simp) with h221 | h221
                                        · rcases p199_3 (m.d 3 5) (by simp) with h222 | h222
                                          · linarith only [h140, h222, hlam]
                                          · linarith only [h131, h222, hlam]
                                        · linarith only [h221, hlam, p199_0]
                                  · linarith only [h1, h216, hlam]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  rcases p199_3 (m.d 0 3) (by simp) with h227 | h227
                                  · rcases p199_3 (m.d 1 3) (by simp) with h228 | h228
                                    · linarith only [h13, h228, hlam]
                                    · linarith only [h10, h228, hlam]
                                  · linarith only [h227, h4, hlam]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h0, h10, h131, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1, p199_1]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h8, hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  rcases p199_3 (m.d 0 3) (by simp) with h235 | h235
                                  · rcases p199_3 (m.d 1 3) (by simp) with h236 | h236
                                    · linarith only [h236, hlam, p199_0]
                                    · rcases p199_3 (m.d 2 3) (by simp) with h238 | h238
                                      · linarith only [h136, h238, hlam]
                                      · rcases p199_3 (m.d 3 4) (by simp) with h240 | h240
                                        · rcases p199_3 (m.d 3 5) (by simp) with h241 | h241
                                          · rcases h5bigk with h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [hlam, p242_0]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h0, h10, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1, p242_1]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              rcases p242_3 (m.d 0 5) (by simp) with h245 | h245
                                              · rcases p242_3 (m.d 1 5) (by simp) with h246 | h246
                                                · linarith only [h246, h3, hlam]
                                                · linarith only [h12, h246, hlam]
                                              · linarith only [h245, h6, hlam]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h0, h10, h131, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p141_1, p242_1]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              rcases p242_3 (m.d 0 5) (by simp) with h251 | h251
                                              · rcases p242_3 (m.d 1 5) (by simp) with h252 | h252
                                                · linarith only [h252, h3, hlam]
                                                · linarith only [h133, h252, hlam]
                                              · linarith only [h251, h9, hlam]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h3, hlam, p242_0]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [hlam, p242_0]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p242_1, u5ehi2]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h131, hlam, p242_1]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h0, h13, h133, h134, h138, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p242_1]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h6, hlam, p242_1]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h12, hlam, p242_1]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [hlam, p242_0]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h136, hlam, p242_1]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h138, hlam, p242_1]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h8, hlam, p242_0]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht5b, p242_1, u5ehi1]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht5b, p242_1, u5ehi2]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [hlam, p242_0]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h0, h134, h138, h140, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p242_1]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h9, hlam, p242_0]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h133, hlam, p242_0]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht5b, p242_1, u5ehi2]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [h140, hlam, p242_0]
                                            · have p242_0 := h242c.1
                                              have p242_1 := h242c.2.1
                                              have p242_2 := h242c.2.2.1
                                              have p242_3 := h242c.2.2.2
                                              linarith only [hlam, p242_0]
                                          · linarith only [h241, hlam, p199_0]
                                        · linarith only [h13, h240, hlam]
                                  · linarith only [h1, h235, hlam]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  rcases p199_3 (m.d 0 3) (by simp) with h279 | h279
                                  · rcases p199_3 (m.d 1 3) (by simp) with h280 | h280
                                    · linarith only [h131, h280, hlam]
                                    · linarith only [h10, h280, hlam]
                                  · linarith only [h279, h4, hlam]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [h140, hlam, p199_0]
                                · have p199_0 := h199c.1
                                  have p199_1 := h199c.2.1
                                  have p199_2 := h199c.2.2.1
                                  have p199_3 := h199c.2.2.2
                                  linarith only [hlam, p199_0]
                              · linarith only [h133, h196, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · linarith only [h10, h196, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p141_1]
                            · linarith only [h131, h195, hlam]
                          · linarith only [h13, h194, hlam]
                      · linarith only [h10, h191, hlam]
                    · linarith only [h1, h190, hlam]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [h133, hlam, p141_0]
                  · have p141_0 := h141c.1
                    have p141_1 := h141c.2.1
                    have p141_2 := h141c.2.2.1
                    have p141_3 := h141c.2.2.2
                    linarith only [hlam, p141_0]
                · linarith only [h13, h133, h140, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h295 | h295
          · linarith only [h10, h13, h295, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h297 | h297
            · linarith only [h10, h131, h297, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h299 | h299
              · linarith only [h0, h11, h13, h133, h299, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h301 | h301
                · rcases h1bigk with h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [hlam, p302_0]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h12, hc01, hlam, hphi, ht0b, ht5b, p302_1, u5ehi2]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h0, h13, h133, h301, h4, h7, hlam, p302_2]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h0, h133, h301, h4, h7, hlam, p302_2]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    rcases p302_3 (m.d 0 1) (by simp) with h307 | h307
                    · rcases p302_3 (m.d 1 2) (by simp) with h308 | h308
                      · linarith only [h0, h308, hlam]
                      · linarith only [h12, h308, hlam]
                    · linarith only [h307, hlam, p302_0]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h0, hlam, p302_0]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [hlam, p302_0]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    rcases p302_3 (m.d 0 1) (by simp) with h314 | h314
                    · rcases p302_3 (m.d 1 2) (by simp) with h315 | h315
                      · rcases p302_3 (m.d 1 3) (by simp) with h316 | h316
                        · linarith only [h10, h316, hlam]
                        · rcases p302_3 (m.d 1 4) (by simp) with h318 | h318
                          · linarith only [h11, h318, hlam]
                          · linarith only [h13, h318, hlam]
                      · linarith only [h10, h315, hlam]
                    · linarith only [h1, h314, hlam]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    rcases p302_3 (m.d 0 1) (by simp) with h323 | h323
                    · rcases p302_3 (m.d 1 2) (by simp) with h324 | h324
                      · rcases p302_3 (m.d 1 3) (by simp) with h325 | h325
                        · linarith only [h10, h325, hlam]
                        · rcases p302_3 (m.d 1 4) (by simp) with h327 | h327
                          · linarith only [h11, h327, hlam]
                          · rcases p302_3 (m.d 1 5) (by simp) with h329 | h329
                            · linarith only [h12, h329, hlam]
                            · linarith only [h133, h329, hlam]
                      · linarith only [h11, h324, hlam]
                    · linarith only [h2, h323, hlam]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h0, h12, hc01, hlam, hphi, ht0b, ht5b, p302_1, u5ehi2]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h1, hlam, p302_0]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h10, hlam, p302_1]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [hlam, p302_0]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h13, hlam, p302_1]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h131, hlam, p302_1]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h2, hlam, p302_0]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h11, hlam, p302_1]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h0, h10, h133, h301, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p302_1]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [hlam, p302_0]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h133, hlam, p302_1]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h3, hlam, p302_0]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h12, hlam, p302_1]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h0, h10, h133, h301, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p302_1]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [h0, h133, h301, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p302_1]
                  · have p302_0 := h302c.1
                    have p302_1 := h302c.2.1
                    have p302_2 := h302c.2.2.1
                    have p302_3 := h302c.2.2.2
                    linarith only [hlam, p302_0]
                · rcases h1bigk with h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [hlam, p350_0]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h12, hc01, hlam, hphi, ht0b, ht5b, p350_1, u5ehi2]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h0, h13, h301, h4, h7, h9, hlam, p350_2]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    rcases p350_3 (m.d 0 1) (by simp) with h354 | h354
                    · rcases p350_3 (m.d 1 2) (by simp) with h355 | h355
                      · linarith only [h0, h355, hlam]
                      · linarith only [h11, h355, hlam]
                    · linarith only [h354, hlam, p350_0]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    rcases p350_3 (m.d 0 1) (by simp) with h359 | h359
                    · rcases p350_3 (m.d 1 2) (by simp) with h360 | h360
                      · linarith only [h0, h360, hlam]
                      · linarith only [h12, h360, hlam]
                    · linarith only [h359, hlam, p350_0]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h0, hlam, p350_0]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [hlam, p350_0]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    rcases p350_3 (m.d 0 1) (by simp) with h366 | h366
                    · rcases p350_3 (m.d 1 2) (by simp) with h367 | h367
                      · rcases p350_3 (m.d 1 3) (by simp) with h368 | h368
                        · linarith only [h10, h368, hlam]
                        · rcases p350_3 (m.d 1 4) (by simp) with h370 | h370
                          · linarith only [h11, h370, hlam]
                          · linarith only [h13, h370, hlam]
                      · linarith only [h10, h367, hlam]
                    · linarith only [h1, h366, hlam]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    rcases p350_3 (m.d 0 1) (by simp) with h375 | h375
                    · rcases p350_3 (m.d 1 2) (by simp) with h376 | h376
                      · rcases p350_3 (m.d 1 3) (by simp) with h377 | h377
                        · linarith only [h10, h377, hlam]
                        · rcases p350_3 (m.d 1 4) (by simp) with h379 | h379
                          · linarith only [h11, h379, hlam]
                          · rcases p350_3 (m.d 1 5) (by simp) with h381 | h381
                            · linarith only [h12, h381, hlam]
                            · linarith only [h133, h381, hlam]
                      · linarith only [h11, h376, hlam]
                    · linarith only [h2, h375, hlam]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p350_1, u5ehi1]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h1, hlam, p350_0]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h10, hlam, p350_1]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [hlam, p350_0]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h13, hlam, p350_1]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h131, hlam, p350_1]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h2, hlam, p350_0]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h11, hlam, p350_1]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h0, h10, h13, h301, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p350_1]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [hlam, p350_0]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h133, hlam, p350_1]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h3, hlam, p350_0]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [h12, hlam, p350_1]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    rcases p350_3 (m.d 0 1) (by simp) with h399 | h399
                    · rcases p350_3 (m.d 1 2) (by simp) with h400 | h400
                      · rcases p350_3 (m.d 1 3) (by simp) with h401 | h401
                        · linarith only [h131, h401, hlam]
                        · rcases p350_3 (m.d 1 4) (by simp) with h403 | h403
                          · linarith only [h133, h403, hlam]
                          · linarith only [h13, h403, hlam]
                      · linarith only [h10, h400, hlam]
                    · linarith only [h1, h399, hlam]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    rcases p350_3 (m.d 0 1) (by simp) with h408 | h408
                    · rcases p350_3 (m.d 1 2) (by simp) with h409 | h409
                      · rcases p350_3 (m.d 1 3) (by simp) with h410 | h410
                        · linarith only [h131, h410, hlam]
                        · rcases p350_3 (m.d 1 4) (by simp) with h412 | h412
                          · linarith only [h133, h412, hlam]
                          · rcases p350_3 (m.d 1 5) (by simp) with h414 | h414
                            · rcases h1emax with h415 | h415 | h415 | h415 | h415
                              · linarith only [h0, h301, h4, h415, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h11, h12, h295, h415, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p350_1]
                              · rcases h3bigk with h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h13, h131, h301, h7, h9, hlam, p350_1, p418_2]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h11, h131, h295, h301, h7, h9, hlam, p350_1, p418_2]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  rcases p418_3 (m.d 0 3) (by simp) with h422 | h422
                                  · rcases p418_3 (m.d 1 3) (by simp) with h423 | h423
                                    · linarith only [h1, h423, hlam]
                                    · rcases p418_3 (m.d 2 3) (by simp) with h425 | h425
                                      · linarith only [h4, h425, hlam]
                                      · rcases p418_3 (m.d 3 4) (by simp) with h427 | h427
                                        · linarith only [h427, hlam, p418_0]
                                        · rcases p418_3 (m.d 3 5) (by simp) with h429 | h429
                                          · linarith only [h429, h8, hlam]
                                          · linarith only [h301, h429, hlam]
                                  · linarith only [h422, hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h0, h11, h131, h295, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p350_1, p418_1]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h1, hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h13, h131, h301, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p350_1, p418_1]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h13, hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h131, hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h4, hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h10, hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h295, hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h297, hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h7, hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h0, h301, h4, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p418_1]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h0, h301, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p418_1]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h301, hlam, p418_1]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h8, hlam, p418_0]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  rcases p418_3 (m.d 0 3) (by simp) with h450 | h450
                                  · rcases p418_3 (m.d 1 3) (by simp) with h451 | h451
                                    · linarith only [h451, hlam, p418_0]
                                    · rcases p418_3 (m.d 2 3) (by simp) with h453 | h453
                                      · linarith only [h297, h453, hlam]
                                      · rcases p418_3 (m.d 3 4) (by simp) with h455 | h455
                                        · linarith only [h301, h455, hlam]
                                        · linarith only [h13, h455, hlam]
                                  · linarith only [h1, h450, hlam]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  rcases p418_3 (m.d 0 3) (by simp) with h459 | h459
                                  · rcases p418_3 (m.d 1 3) (by simp) with h460 | h460
                                    · linarith only [h131, h460, hlam]
                                    · linarith only [h10, h460, hlam]
                                  · linarith only [h4, h459, hlam]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [h0, h10, h13, h301, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p418_1]
                                · have p418_0 := h418c.1
                                  have p418_1 := h418c.2.1
                                  have p418_2 := h418c.2.2.1
                                  have p418_3 := h418c.2.2.2
                                  linarith only [hlam, p418_0]
                              · rcases h3bigk with h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h13, h131, h301, h7, h9, hlam, p350_1, p466_2]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h11, h131, h295, h301, h7, h9, hlam, p350_1, p466_2]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  rcases p466_3 (m.d 0 3) (by simp) with h470 | h470
                                  · rcases p466_3 (m.d 1 3) (by simp) with h471 | h471
                                    · linarith only [h1, h471, hlam]
                                    · rcases p466_3 (m.d 2 3) (by simp) with h473 | h473
                                      · linarith only [h4, h473, hlam]
                                      · rcases p466_3 (m.d 3 4) (by simp) with h475 | h475
                                        · linarith only [h475, hlam, p466_0]
                                        · rcases p466_3 (m.d 3 5) (by simp) with h477 | h477
                                          · linarith only [h477, h8, hlam]
                                          · linarith only [h301, h477, hlam]
                                  · linarith only [h470, hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h0, h13, h131, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p350_1, p466_1]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h1, hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h0, h13, h301, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p466_1]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h13, hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h131, hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h4, hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h10, hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h295, hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h297, hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h7, hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h0, h301, h4, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p466_1]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h0, h301, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p466_1]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h301, hlam, p466_1]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h8, hlam, p466_0]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  rcases p466_3 (m.d 0 3) (by simp) with h498 | h498
                                  · rcases p466_3 (m.d 1 3) (by simp) with h499 | h499
                                    · linarith only [h499, hlam, p466_0]
                                    · rcases p466_3 (m.d 2 3) (by simp) with h501 | h501
                                      · linarith only [h297, h501, hlam]
                                      · rcases p466_3 (m.d 3 4) (by simp) with h503 | h503
                                        · linarith only [h301, h503, hlam]
                                        · linarith only [h13, h503, hlam]
                                  · linarith only [h1, h498, hlam]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  rcases p466_3 (m.d 0 3) (by simp) with h507 | h507
                                  · rcases p466_3 (m.d 1 3) (by simp) with h508 | h508
                                    · linarith only [h131, h508, hlam]
                                    · linarith only [h10, h508, hlam]
                                  · linarith only [h4, h507, hlam]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [h10, h13, hc23, hc35, hlam, hphi, p466_1]
                                · have p466_0 := h466c.1
                                  have p466_1 := h466c.2.1
                                  have p466_2 := h466c.2.2.1
                                  have p466_3 := h466c.2.2.2
                                  linarith only [hlam, p466_0]
                              · linarith only [h11, h295, h415, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p350_1]
                            · linarith only [h133, h414, hlam]
                      · linarith only [h11, h409, hlam]
                    · linarith only [h2, h408, hlam]
                  · have p350_0 := h350c.1
                    have p350_1 := h350c.2.1
                    have p350_2 := h350c.2.2.1
                    have p350_3 := h350c.2.2.2
                    linarith only [hlam, p350_0]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h519 | h519
    · rcases m.htr 1 3 5 (by decide) (by decide) with h520 | h520
      · linarith only [h0, h10, h12, h520, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h522 | h522
        · linarith only [h0, h11, h12, h522, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h524 | h524
          · linarith only [h0, h10, h12, h524, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h10, h12, h519, h524, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h527 | h527
      · linarith only [h0, h11, h12, h519, h527, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h529 | h529
        · linarith only [h0, h11, h12, h529, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h531 | h531
          · linarith only [h0, h10, h12, h519, h531, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h533 | h533
            · linarith only [h0, h10, h12, h527, h533, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h535 | h535
              · linarith only [h0, h11, h12, h4, h533, h535, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h537 | h537
                · linarith only [h11, h12, h531, h535, h537, hc23, hc34, hlam, hphi]
                · rcases h1bigk with h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    rcases p539_3 (m.d 0 1) (by simp) with h541 | h541
                    · rcases p539_3 (m.d 1 2) (by simp) with h542 | h542
                      · linarith only [h542, hlam, p539_0]
                      · rcases p539_3 (m.d 1 3) (by simp) with h544 | h544
                        · linarith only [h1, h544, hlam]
                        · rcases p539_3 (m.d 1 4) (by simp) with h546 | h546
                          · linarith only [h2, h546, hlam]
                          · rcases p539_3 (m.d 1 5) (by simp) with h548 | h548
                            · linarith only [h3, h548, hlam]
                            · linarith only [h12, h548, hlam]
                    · linarith only [h541, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h0, h4, h519, h537, h7, h9, hlam, p539_2]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    rcases p539_3 (m.d 0 1) (by simp) with h553 | h553
                    · rcases p539_3 (m.d 1 2) (by simp) with h554 | h554
                      · linarith only [h0, h554, hlam]
                      · linarith only [h11, h554, hlam]
                    · linarith only [h553, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    rcases p539_3 (m.d 0 1) (by simp) with h558 | h558
                    · rcases p539_3 (m.d 1 2) (by simp) with h559 | h559
                      · linarith only [h0, h559, hlam]
                      · rcases p539_3 (m.d 1 3) (by simp) with h561 | h561
                        · linarith only [h1, h561, hlam]
                        · rcases p539_3 (m.d 1 4) (by simp) with h563 | h563
                          · linarith only [h2, h563, hlam]
                          · rcases p539_3 (m.d 1 5) (by simp) with h565 | h565
                            · linarith only [h565, hlam, p539_0]
                            · rcases h1emax with h567 | h567 | h567 | h567 | h567
                              · linarith only [h0, h11, h12, h4, h531, h533, h537, h567, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases h3bigk with h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c | h569c
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h519, h537, h7, h9, hlam, p569_2]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h11, h12, h531, h533, h537, h7, h9, hlam, p569_2]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  rcases p569_3 (m.d 0 3) (by simp) with h573 | h573
                                  · rcases p569_3 (m.d 1 3) (by simp) with h574 | h574
                                    · linarith only [h1, h574, hlam]
                                    · rcases p569_3 (m.d 2 3) (by simp) with h576 | h576
                                      · linarith only [h4, h576, hlam]
                                      · rcases p569_3 (m.d 3 4) (by simp) with h578 | h578
                                        · linarith only [h578, hlam, p569_0]
                                        · rcases p569_3 (m.d 3 5) (by simp) with h580 | h580
                                          · linarith only [h580, h8, hlam]
                                          · linarith only [h537, h580, hlam]
                                  · linarith only [h573, hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h0, h11, h12, h4, h531, h533, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p569_1]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h1, hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h519, h537, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p569_1]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h519, hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h527, hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h4, hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h10, hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h531, hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h533, hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h7, hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h537, h9, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p569_1]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h0, h4, h537, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p569_1]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h537, hlam, p569_1]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h8, hlam, p569_0]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  rcases p569_3 (m.d 0 3) (by simp) with h601 | h601
                                  · rcases p569_3 (m.d 1 3) (by simp) with h602 | h602
                                    · linarith only [h602, hlam, p569_0]
                                    · rcases p569_3 (m.d 2 3) (by simp) with h604 | h604
                                      · linarith only [h533, h604, hlam]
                                      · rcases p569_3 (m.d 3 4) (by simp) with h606 | h606
                                        · linarith only [h537, h606, hlam]
                                        · linarith only [h519, h606, hlam]
                                  · linarith only [h1, h601, hlam]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  rcases p569_3 (m.d 0 3) (by simp) with h610 | h610
                                  · rcases p569_3 (m.d 1 3) (by simp) with h611 | h611
                                    · linarith only [h527, h611, hlam]
                                    · linarith only [h10, h611, hlam]
                                  · linarith only [h4, h610, hlam]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [h0, h10, h4, h519, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p569_1]
                                · have p569_0 := h569c.1
                                  have p569_1 := h569c.2.1
                                  have p569_2 := h569c.2.2.1
                                  have p569_3 := h569c.2.2.2
                                  linarith only [hlam, p569_0]
                              · rcases h3bigk with h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c | h617c
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h519, h537, h7, h9, hlam, p617_2]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h11, h12, h531, h533, h537, h7, h9, hlam, p617_2]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  rcases p617_3 (m.d 0 3) (by simp) with h621 | h621
                                  · rcases p617_3 (m.d 1 3) (by simp) with h622 | h622
                                    · linarith only [h1, h622, hlam]
                                    · rcases p617_3 (m.d 2 3) (by simp) with h624 | h624
                                      · linarith only [h4, h624, hlam]
                                      · rcases p617_3 (m.d 3 4) (by simp) with h626 | h626
                                        · linarith only [h626, hlam, p617_0]
                                        · rcases p617_3 (m.d 3 5) (by simp) with h628 | h628
                                          · linarith only [h628, h8, hlam]
                                          · linarith only [h537, h628, hlam]
                                  · linarith only [h621, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h11, h12, h4, h531, h533, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h1, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h4, h519, h537, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h519, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h527, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h4, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h10, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h531, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h533, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h7, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h4, h537, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h4, h537, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h537, hlam, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h8, hlam, p617_0]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  rcases p617_3 (m.d 0 3) (by simp) with h649 | h649
                                  · rcases p617_3 (m.d 1 3) (by simp) with h650 | h650
                                    · linarith only [h650, hlam, p617_0]
                                    · rcases p617_3 (m.d 2 3) (by simp) with h652 | h652
                                      · linarith only [h533, h652, hlam]
                                      · rcases p617_3 (m.d 3 4) (by simp) with h654 | h654
                                        · linarith only [h537, h654, hlam]
                                        · linarith only [h519, h654, hlam]
                                  · linarith only [h1, h649, hlam]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  rcases p617_3 (m.d 0 3) (by simp) with h658 | h658
                                  · rcases p617_3 (m.d 1 3) (by simp) with h659 | h659
                                    · linarith only [h527, h659, hlam]
                                    · linarith only [h10, h659, hlam]
                                  · linarith only [h4, h658, hlam]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [h0, h10, h4, h519, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p617_1]
                                · have p617_0 := h617c.1
                                  have p617_1 := h617c.2.1
                                  have p617_2 := h617c.2.2.1
                                  have p617_3 := h617c.2.2.2
                                  linarith only [hlam, p617_0]
                              · rcases h3bigk with h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h519, h537, h7, h9, hlam, p665_2]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h11, h12, h531, h533, h537, h7, h9, hlam, p665_2]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  rcases p665_3 (m.d 0 3) (by simp) with h669 | h669
                                  · rcases p665_3 (m.d 1 3) (by simp) with h670 | h670
                                    · linarith only [h1, h670, hlam]
                                    · rcases p665_3 (m.d 2 3) (by simp) with h672 | h672
                                      · linarith only [h4, h672, hlam]
                                      · rcases p665_3 (m.d 3 4) (by simp) with h674 | h674
                                        · linarith only [h674, hlam, p665_0]
                                        · rcases p665_3 (m.d 3 5) (by simp) with h676 | h676
                                          · linarith only [h676, h8, hlam]
                                          · linarith only [h537, h676, hlam]
                                  · linarith only [h669, hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h0, h11, h12, h4, h531, h533, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p665_1]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h1, hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h0, h4, h519, h537, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p665_1]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h519, hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h527, hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h4, hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h10, hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h531, hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h533, hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h7, hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h0, h4, h537, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p665_1]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h0, h4, h537, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p665_1]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h537, hlam, p665_1]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h8, hlam, p665_0]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  rcases p665_3 (m.d 0 3) (by simp) with h697 | h697
                                  · rcases p665_3 (m.d 1 3) (by simp) with h698 | h698
                                    · linarith only [h698, hlam, p665_0]
                                    · rcases p665_3 (m.d 2 3) (by simp) with h700 | h700
                                      · linarith only [h533, h700, hlam]
                                      · rcases p665_3 (m.d 3 4) (by simp) with h702 | h702
                                        · linarith only [h537, h702, hlam]
                                        · linarith only [h519, h702, hlam]
                                  · linarith only [h1, h697, hlam]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  rcases p665_3 (m.d 0 3) (by simp) with h706 | h706
                                  · rcases p665_3 (m.d 1 3) (by simp) with h707 | h707
                                    · linarith only [h527, h707, hlam]
                                    · linarith only [h10, h707, hlam]
                                  · linarith only [h4, h706, hlam]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [h10, h519, hc23, hc35, hlam, hphi, p665_1]
                                · have p665_0 := h665c.1
                                  have p665_1 := h665c.2.1
                                  have p665_2 := h665c.2.2.1
                                  have p665_3 := h665c.2.2.2
                                  linarith only [hlam, p665_0]
                              · rcases h3bigk with h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c | h713c
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h519, h537, h7, h9, hlam, p713_2]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h11, h12, h531, h533, h537, h7, h9, hlam, p713_2]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  rcases p713_3 (m.d 0 3) (by simp) with h717 | h717
                                  · rcases p713_3 (m.d 1 3) (by simp) with h718 | h718
                                    · linarith only [h1, h718, hlam]
                                    · rcases p713_3 (m.d 2 3) (by simp) with h720 | h720
                                      · linarith only [h4, h720, hlam]
                                      · rcases p713_3 (m.d 3 4) (by simp) with h722 | h722
                                        · linarith only [h722, hlam, p713_0]
                                        · rcases p713_3 (m.d 3 5) (by simp) with h724 | h724
                                          · linarith only [h724, h8, hlam]
                                          · linarith only [h537, h724, hlam]
                                  · linarith only [h717, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h11, h12, h4, h531, h533, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h1, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h4, h519, h537, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h519, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h527, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h4, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h10, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h531, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h533, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h7, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h4, h537, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h0, h4, h537, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h537, hlam, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h8, hlam, p713_0]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  rcases p713_3 (m.d 0 3) (by simp) with h745 | h745
                                  · rcases p713_3 (m.d 1 3) (by simp) with h746 | h746
                                    · linarith only [h746, hlam, p713_0]
                                    · rcases p713_3 (m.d 2 3) (by simp) with h748 | h748
                                      · linarith only [h533, h748, hlam]
                                      · rcases p713_3 (m.d 3 4) (by simp) with h750 | h750
                                        · linarith only [h537, h750, hlam]
                                        · linarith only [h519, h750, hlam]
                                  · linarith only [h1, h745, hlam]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  rcases p713_3 (m.d 0 3) (by simp) with h754 | h754
                                  · rcases p713_3 (m.d 1 3) (by simp) with h755 | h755
                                    · linarith only [h527, h755, hlam]
                                    · linarith only [h10, h755, hlam]
                                  · linarith only [h4, h754, hlam]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [h10, h519, hc23, hc35, hlam, hphi, p713_1]
                                · have p713_0 := h713c.1
                                  have p713_1 := h713c.2.1
                                  have p713_2 := h713c.2.2.1
                                  have p713_3 := h713c.2.2.2
                                  linarith only [hlam, p713_0]
                    · linarith only [h558, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h0, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h0, h10, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h0, h12, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h12, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h1, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h10, hlam, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h519, hlam, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h527, hlam, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h2, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h11, hlam, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h0, h10, h11, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h529, hlam, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h3, hlam, p539_0]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [h10, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p539_1]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    rcases p539_3 (m.d 0 1) (by simp) with h779 | h779
                    · rcases p539_3 (m.d 1 2) (by simp) with h780 | h780
                      · linarith only [h12, h780, hlam]
                      · linarith only [h10, h780, hlam]
                    · linarith only [h1, h779, hlam]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    rcases p539_3 (m.d 0 1) (by simp) with h784 | h784
                    · rcases p539_3 (m.d 1 2) (by simp) with h785 | h785
                      · linarith only [h12, h785, hlam]
                      · linarith only [h11, h785, hlam]
                    · linarith only [h2, h784, hlam]
                  · have p539_0 := h539c.1
                    have p539_1 := h539c.2.1
                    have p539_2 := h539c.2.2.1
                    have p539_3 := h539c.2.2.2
                    linarith only [hlam, p539_0]

end R2N4
