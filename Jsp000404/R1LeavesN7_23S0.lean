import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
  · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
    · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
      · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
        · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
          · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
            · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
              · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                · linarith only [h0, h10, h16, h19, hc01, hc45, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h10, h16, h18, h19, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                · linarith only [h0, h10, h13, h18, h22, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h2bigk with h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h0, h10, h17, hc01, hc35, hlam, hphi, ht0b, ht5b, p24_1]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    rcases p24_3 (m.d 0 2) (by simp) with h27 | h27
                    · rcases p24_3 (m.d 1 2) (by simp) with h28 | h28
                      · linarith only [h0, h28, hlam]
                      · linarith only [h10, h28, hlam]
                    · linarith only [h27, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    rcases p24_3 (m.d 0 2) (by simp) with h32 | h32
                    · rcases p24_3 (m.d 1 2) (by simp) with h33 | h33
                      · linarith only [h0, h33, hlam]
                      · linarith only [h11, h33, hlam]
                    · linarith only [h32, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    rcases p24_3 (m.d 0 2) (by simp) with h37 | h37
                    · rcases p24_3 (m.d 1 2) (by simp) with h38 | h38
                      · linarith only [h0, h38, hlam]
                      · linarith only [h12, h38, hlam]
                    · linarith only [h37, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h0, hlam, p24_1]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h0, h17, h22, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    rcases p24_3 (m.d 0 2) (by simp) with h45 | h45
                    · rcases p24_3 (m.d 1 2) (by simp) with h46 | h46
                      · rcases p24_3 (m.d 2 3) (by simp) with h47 | h47
                        · linarith only [h10, h47, hlam]
                        · linarith only [h16, h47, hlam]
                      · linarith only [h46, hlam, p24_0]
                    · linarith only [h45, h5, hlam]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    rcases p24_3 (m.d 0 2) (by simp) with h52 | h52
                    · rcases p24_3 (m.d 1 2) (by simp) with h53 | h53
                      · rcases p24_3 (m.d 2 3) (by simp) with h54 | h54
                        · linarith only [h10, h54, hlam]
                        · linarith only [h17, h54, hlam]
                      · linarith only [h53, hlam, p24_0]
                    · linarith only [h52, h6, hlam]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h4, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h10, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h0, h10, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p24_1]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h5, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h11, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h16, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h18, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h6, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h12, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h17, hlam, p24_0]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [h0, h12, h16, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p24_1]
                  · have p24_0 := h24c.1
                    have p24_1 := h24c.2.1
                    have p24_2 := h24c.2.2.1
                    have p24_3 := h24c.2.2.2
                    linarith only [hlam, p24_0]
            · linarith only [h1, h14, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
            · linarith only [h0, h10, h13, h16, h75, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h77 | h77
              · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                · rcases h2bigk with h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c | h79c
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h10, h13, h75, h78, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p79_1]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    rcases p79_3 (m.d 0 2) (by simp) with h82 | h82
                    · rcases p79_3 (m.d 1 2) (by simp) with h83 | h83
                      · linarith only [h0, h83, hlam]
                      · linarith only [h10, h83, hlam]
                    · linarith only [h82, hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    rcases p79_3 (m.d 0 2) (by simp) with h87 | h87
                    · rcases p79_3 (m.d 1 2) (by simp) with h88 | h88
                      · linarith only [h0, h88, hlam]
                      · linarith only [h11, h88, hlam]
                    · linarith only [h87, hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    rcases p79_3 (m.d 0 2) (by simp) with h92 | h92
                    · rcases p79_3 (m.d 1 2) (by simp) with h93 | h93
                      · linarith only [h0, h93, hlam]
                      · linarith only [h12, h93, hlam]
                    · linarith only [h92, hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h0, hlam, p79_1]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    rcases p79_3 (m.d 0 2) (by simp) with h99 | h99
                    · rcases p79_3 (m.d 1 2) (by simp) with h100 | h100
                      · rcases p79_3 (m.d 2 3) (by simp) with h101 | h101
                        · linarith only [h101, hlam, p79_0]
                        · rcases p79_3 (m.d 2 4) (by simp) with h103 | h103
                          · linarith only [h103, h11, hlam]
                          · linarith only [h103, h16, hlam]
                      · linarith only [h100, hlam, p79_0]
                    · linarith only [h4, h99, hlam]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h0, h77, hc01, hc45, hlam, hphi, ht0b, ht5b, p79_1]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    rcases p79_3 (m.d 0 2) (by simp) with h109 | h109
                    · rcases p79_3 (m.d 1 2) (by simp) with h110 | h110
                      · rcases p79_3 (m.d 2 3) (by simp) with h111 | h111
                        · linarith only [h10, h111, hlam]
                        · rcases p79_3 (m.d 2 4) (by simp) with h113 | h113
                          · linarith only [h11, h113, hlam]
                          · linarith only [h113, h77, hlam]
                      · linarith only [h110, hlam, p79_0]
                    · linarith only [h109, h6, hlam]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h4, hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h10, hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h16, hlam, p79_1]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h75, hlam, p79_1]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h5, hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h11, hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p79_1]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h1, h13, h16, hc01, hc25, hlam, hphi, ht0b, ht5b, p79_1]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h6, hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h12, hlam, p79_0]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p79_1]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [h77, hlam, p79_1]
                  · have p79_0 := h79c.1
                    have p79_1 := h79c.2.1
                    have p79_2 := h79c.2.2.1
                    have p79_3 := h79c.2.2.2
                    linarith only [hlam, p79_0]
                · linarith only [h0, h10, h13, h15, h16, h78, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                · linarith only [h0, h10, h13, h134, h77, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h10, h13, h134, h15, h16, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h137 | h137
          · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
            · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
              · linarith only [h139, h15, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                · linarith only [h137, h141, h15, hc23, hlam, hphi, ht12, u1ehi3]
                · rcases h2bigk with h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c | h143c
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h0, h10, h138, h141, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    rcases p143_3 (m.d 0 2) (by simp) with h146 | h146
                    · rcases p143_3 (m.d 1 2) (by simp) with h147 | h147
                      · linarith only [h0, h147, hlam]
                      · linarith only [h10, h147, hlam]
                    · linarith only [h146, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    rcases p143_3 (m.d 0 2) (by simp) with h151 | h151
                    · rcases p143_3 (m.d 1 2) (by simp) with h152 | h152
                      · linarith only [h0, h152, hlam]
                      · linarith only [h11, h152, hlam]
                    · linarith only [h151, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    rcases p143_3 (m.d 0 2) (by simp) with h156 | h156
                    · rcases p143_3 (m.d 1 2) (by simp) with h157 | h157
                      · linarith only [h0, h157, hlam]
                      · linarith only [h12, h157, hlam]
                    · linarith only [h156, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h0, hlam, p143_1]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h0, h138, h141, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    rcases p143_3 (m.d 0 2) (by simp) with h164 | h164
                    · rcases p143_3 (m.d 1 2) (by simp) with h165 | h165
                      · rcases p143_3 (m.d 2 3) (by simp) with h166 | h166
                        · linarith only [h10, h166, hlam]
                        · linarith only [h137, h166, hlam]
                      · linarith only [h165, hlam, p143_0]
                    · linarith only [h164, h5, hlam]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    rcases p143_3 (m.d 0 2) (by simp) with h171 | h171
                    · rcases p143_3 (m.d 1 2) (by simp) with h172 | h172
                      · rcases p143_3 (m.d 2 3) (by simp) with h173 | h173
                        · linarith only [h10, h173, hlam]
                        · linarith only [h138, h173, hlam]
                      · linarith only [h172, hlam, p143_0]
                    · linarith only [h171, h6, hlam]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h4, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h10, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p143_1]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p143_1]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h5, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h11, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h137, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h139, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h6, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h12, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h138, hlam, p143_0]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [h0, h12, h137, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p143_1]
                  · have p143_0 := h143c.1
                    have p143_1 := h143c.2.1
                    have p143_2 := h143c.2.2.1
                    have p143_3 := h143c.2.2.2
                    linarith only [hlam, p143_0]
            · linarith only [h0, h10, h137, h138, h14, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
            · linarith only [h0, h13, h137, h15, h194, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h196 | h196
              · linarith only [h13, h137, h15, h196, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h198 | h198
                · linarith only [h13, h15, h198, hlam]
                · rcases h2bigk with h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h10, h13, h137, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h13, h137, h15, h4, h7, h9, hlam, p200_2]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    rcases p200_3 (m.d 0 2) (by simp) with h204 | h204
                    · rcases p200_3 (m.d 1 2) (by simp) with h205 | h205
                      · linarith only [h0, h205, hlam]
                      · linarith only [h11, h205, hlam]
                    · linarith only [h204, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    rcases p200_3 (m.d 0 2) (by simp) with h209 | h209
                    · rcases p200_3 (m.d 1 2) (by simp) with h210 | h210
                      · linarith only [h0, h210, hlam]
                      · linarith only [h12, h210, hlam]
                    · linarith only [h209, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    rcases p200_3 (m.d 0 2) (by simp) with h216 | h216
                    · rcases p200_3 (m.d 1 2) (by simp) with h217 | h217
                      · rcases p200_3 (m.d 2 3) (by simp) with h218 | h218
                        · linarith only [h218, hlam, p200_0]
                        · rcases p200_3 (m.d 2 4) (by simp) with h220 | h220
                          · linarith only [h11, h220, hlam]
                          · linarith only [h137, h220, hlam]
                      · linarith only [h217, hlam, p200_0]
                    · linarith only [h216, h4, hlam]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    rcases p200_3 (m.d 0 2) (by simp) with h225 | h225
                    · rcases p200_3 (m.d 1 2) (by simp) with h226 | h226
                      · rcases p200_3 (m.d 2 3) (by simp) with h227 | h227
                        · linarith only [h10, h227, hlam]
                        · rcases p200_3 (m.d 2 4) (by simp) with h229 | h229
                          · linarith only [h229, hlam, p200_0]
                          · rcases p200_3 (m.d 2 5) (by simp) with h231 | h231
                            · linarith only [h12, h231, hlam]
                            · linarith only [h196, h231, hlam]
                      · linarith only [h226, hlam, p200_0]
                    · linarith only [h225, h5, hlam]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    rcases p200_3 (m.d 0 2) (by simp) with h236 | h236
                    · rcases p200_3 (m.d 1 2) (by simp) with h237 | h237
                      · rcases p200_3 (m.d 2 3) (by simp) with h238 | h238
                        · linarith only [h10, h238, hlam]
                        · rcases p200_3 (m.d 2 4) (by simp) with h240 | h240
                          · linarith only [h11, h240, hlam]
                          · rcases p200_3 (m.d 2 5) (by simp) with h242 | h242
                            · linarith only [h242, hlam, p200_0]
                            · rcases h2emax with h244 | h244 | h244 | h244 | h244
                              · linarith only [h15, h244, h4, h7, h9, hlam, ht12, u1ehi3]
                              · linarith only [h0, h10, h137, h14, h15, h198, h244, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, u1ehi3]
                              · rcases h4bigk with h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c | h247c
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  rcases p247_3 (m.d 0 4) (by simp) with h249 | h249
                                  · rcases p247_3 (m.d 1 4) (by simp) with h250 | h250
                                    · linarith only [h2, h250, hlam]
                                    · rcases p247_3 (m.d 2 4) (by simp) with h252 | h252
                                      · linarith only [h252, h5, hlam]
                                      · rcases p247_3 (m.d 3 4) (by simp) with h254 | h254
                                        · linarith only [h254, h7, hlam]
                                        · rcases p247_3 (m.d 4 5) (by simp) with h256 | h256
                                          · linarith only [h256, h9, hlam]
                                          · linarith only [h15, h256, hlam]
                                  · linarith only [h2, h249, hlam]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  rcases p247_3 (m.d 0 4) (by simp) with h260 | h260
                                  · rcases p247_3 (m.d 1 4) (by simp) with h261 | h261
                                    · linarith only [h2, h261, hlam]
                                    · linarith only [h11, h261, hlam]
                                  · linarith only [h260, h5, hlam]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  rcases p247_3 (m.d 0 4) (by simp) with h265 | h265
                                  · rcases p247_3 (m.d 1 4) (by simp) with h266 | h266
                                    · linarith only [h2, h266, hlam]
                                    · linarith only [h13, h266, hlam]
                                  · linarith only [h265, h7, hlam]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h0, h15, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p247_1, u1ehi3]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h2, hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h15, hc24, hc45, hlam, hphi, p247_1]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h0, h137, h15, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p247_1]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h15, hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h5, hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h11, hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h137, hlam, p247_1]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h196, hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h7, hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h13, hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h0, h10, h14, h198, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p247_1]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h198, hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h9, hlam, p247_0]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p247_1, u1ehi3]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  rcases p247_3 (m.d 0 4) (by simp) with h288 | h288
                                  · rcases p247_3 (m.d 1 4) (by simp) with h289 | h289
                                    · linarith only [h15, h289, hlam]
                                    · linarith only [h11, h289, hlam]
                                  · linarith only [h288, h5, hlam]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [h0, h137, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p247_1]
                                · have p247_0 := h247c.1
                                  have p247_1 := h247c.2.1
                                  have p247_2 := h247c.2.2.1
                                  have p247_3 := h247c.2.2.2
                                  linarith only [hlam, p247_0]
                              · rcases h4bigk with h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c | h295c
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  rcases p295_3 (m.d 0 4) (by simp) with h297 | h297
                                  · rcases p295_3 (m.d 1 4) (by simp) with h298 | h298
                                    · linarith only [h2, h298, hlam]
                                    · rcases p295_3 (m.d 2 4) (by simp) with h300 | h300
                                      · linarith only [h300, h5, hlam]
                                      · rcases p295_3 (m.d 3 4) (by simp) with h302 | h302
                                        · linarith only [h302, h7, hlam]
                                        · rcases p295_3 (m.d 4 5) (by simp) with h304 | h304
                                          · linarith only [h304, h9, hlam]
                                          · linarith only [h15, h304, hlam]
                                  · linarith only [h2, h297, hlam]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  rcases p295_3 (m.d 0 4) (by simp) with h308 | h308
                                  · rcases p295_3 (m.d 1 4) (by simp) with h309 | h309
                                    · linarith only [h2, h309, hlam]
                                    · linarith only [h11, h309, hlam]
                                  · linarith only [h308, h5, hlam]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  rcases p295_3 (m.d 0 4) (by simp) with h313 | h313
                                  · rcases p295_3 (m.d 1 4) (by simp) with h314 | h314
                                    · linarith only [h2, h314, hlam]
                                    · linarith only [h13, h314, hlam]
                                  · linarith only [h313, h7, hlam]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h0, h15, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p295_1, u1ehi3]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h2, hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h15, hc24, hc45, hlam, hphi, p295_1]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h0, h137, h15, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h15, hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h5, hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h11, hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h137, hlam, p295_1]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h196, hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h7, hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h13, hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h0, h10, h13, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p295_1]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h198, hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h9, hlam, p295_0]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p295_1, u1ehi3]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  rcases p295_3 (m.d 0 4) (by simp) with h336 | h336
                                  · rcases p295_3 (m.d 1 4) (by simp) with h337 | h337
                                    · linarith only [h15, h337, hlam]
                                    · linarith only [h11, h337, hlam]
                                  · linarith only [h336, h5, hlam]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [h0, h137, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p295_1]
                                · have p295_0 := h295c.1
                                  have p295_1 := h295c.2.1
                                  have p295_2 := h295c.2.2.1
                                  have p295_3 := h295c.2.2.2
                                  linarith only [hlam, p295_0]
                              · rcases h4bigk with h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  rcases p343_3 (m.d 0 4) (by simp) with h345 | h345
                                  · rcases p343_3 (m.d 1 4) (by simp) with h346 | h346
                                    · linarith only [h2, h346, hlam]
                                    · rcases p343_3 (m.d 2 4) (by simp) with h348 | h348
                                      · linarith only [h348, h5, hlam]
                                      · rcases p343_3 (m.d 3 4) (by simp) with h350 | h350
                                        · linarith only [h350, h7, hlam]
                                        · rcases p343_3 (m.d 4 5) (by simp) with h352 | h352
                                          · linarith only [h352, h9, hlam]
                                          · linarith only [h15, h352, hlam]
                                  · linarith only [h2, h345, hlam]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  rcases p343_3 (m.d 0 4) (by simp) with h356 | h356
                                  · rcases p343_3 (m.d 1 4) (by simp) with h357 | h357
                                    · linarith only [h2, h357, hlam]
                                    · linarith only [h11, h357, hlam]
                                  · linarith only [h356, h5, hlam]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  rcases p343_3 (m.d 0 4) (by simp) with h361 | h361
                                  · rcases p343_3 (m.d 1 4) (by simp) with h362 | h362
                                    · linarith only [h2, h362, hlam]
                                    · linarith only [h13, h362, hlam]
                                  · linarith only [h361, h7, hlam]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h0, h15, h4, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p343_1, u1ehi3]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h2, hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h15, hc24, hc45, hlam, hphi, p343_1]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h0, h137, h15, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h15, hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h5, hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h11, hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h137, hlam, p343_1]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h196, hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h7, hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h13, hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h0, h10, h13, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p343_1]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h198, hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h9, hlam, p343_0]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p343_1, u1ehi3]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  rcases p343_3 (m.d 0 4) (by simp) with h384 | h384
                                  · rcases p343_3 (m.d 1 4) (by simp) with h385 | h385
                                    · linarith only [h15, h385, hlam]
                                    · linarith only [h11, h385, hlam]
                                  · linarith only [h384, h5, hlam]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [h0, h137, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1]
                                · have p343_0 := h343c.1
                                  have p343_1 := h343c.2.1
                                  have p343_2 := h343c.2.2.1
                                  have p343_3 := h343c.2.2.2
                                  linarith only [hlam, p343_0]
                      · linarith only [h237, hlam, p200_0]
                    · linarith only [h236, h6, hlam]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h4, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h10, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h137, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h194, hlam, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h5, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h11, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h196, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h6, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h12, hlam, p200_0]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p200_1]
                  · have p200_0 := h200c.1
                    have p200_1 := h200c.2.1
                    have p200_2 := h200c.2.2.1
                    have p200_3 := h200c.2.2.2
                    linarith only [hlam, p200_0]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
        · linarith only [h13, h14, h408, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h410 | h410
          · rcases m.htr 2 3 5 (by decide) (by decide) with h411 | h411
            · linarith only [h13, h14, h411, hc23, hlam, hphi, ht12, u1ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h413 | h413
              · linarith only [h408, h413, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h415 | h415
                · linarith only [h408, h415, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · rcases h2bigk with h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, h10, h410, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    rcases p417_3 (m.d 0 2) (by simp) with h420 | h420
                    · rcases p417_3 (m.d 1 2) (by simp) with h421 | h421
                      · linarith only [h0, h421, hlam]
                      · linarith only [h10, h421, hlam]
                    · linarith only [h420, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    rcases p417_3 (m.d 0 2) (by simp) with h425 | h425
                    · rcases p417_3 (m.d 1 2) (by simp) with h426 | h426
                      · linarith only [h0, h426, hlam]
                      · linarith only [h11, h426, hlam]
                    · linarith only [h425, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    rcases p417_3 (m.d 0 2) (by simp) with h430 | h430
                    · rcases p417_3 (m.d 1 2) (by simp) with h431 | h431
                      · linarith only [h0, h431, hlam]
                      · linarith only [h12, h431, hlam]
                    · linarith only [h430, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, hlam, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, h410, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    rcases p417_3 (m.d 0 2) (by simp) with h438 | h438
                    · rcases p417_3 (m.d 1 2) (by simp) with h439 | h439
                      · rcases p417_3 (m.d 2 3) (by simp) with h440 | h440
                        · linarith only [h10, h440, hlam]
                        · linarith only [h410, h440, hlam]
                      · linarith only [h439, hlam, p417_0]
                    · linarith only [h438, h5, hlam]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, h410, h411, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h4, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h10, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h411, hlam, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h5, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h11, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h410, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h413, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h6, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h12, hlam, p417_0]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [h0, h12, h410, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p417_1]
                  · have p417_0 := h417c.1
                    have p417_1 := h417c.2.1
                    have p417_2 := h417c.2.2.1
                    have p417_3 := h417c.2.2.2
                    linarith only [hlam, p417_0]
          · linarith only [h13, h14, h410, hc23, hc35, hlam, hphi]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h462 | h462
      · rcases m.htr 1 4 5 (by decide) (by decide) with h463 | h463
        · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
          · linarith only [h13, h464, hc23, hlam, hphi, ht12, u1ehi2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h466 | h466
            · rcases m.htr 2 4 5 (by decide) (by decide) with h467 | h467
              · rcases m.htr 3 4 5 (by decide) (by decide) with h468 | h468
                · rcases h2bigk with h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c | h469c
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h0, h10, h466, hc01, hc35, hlam, hphi, ht0b, ht5b, p469_1]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    rcases p469_3 (m.d 0 2) (by simp) with h472 | h472
                    · rcases p469_3 (m.d 1 2) (by simp) with h473 | h473
                      · linarith only [h0, h473, hlam]
                      · linarith only [h10, h473, hlam]
                    · linarith only [h472, hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    rcases p469_3 (m.d 0 2) (by simp) with h477 | h477
                    · rcases p469_3 (m.d 1 2) (by simp) with h478 | h478
                      · linarith only [h0, h478, hlam]
                      · linarith only [h11, h478, hlam]
                    · linarith only [h477, hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    rcases p469_3 (m.d 0 2) (by simp) with h482 | h482
                    · rcases p469_3 (m.d 1 2) (by simp) with h483 | h483
                      · linarith only [h0, h483, hlam]
                      · linarith only [h12, h483, hlam]
                    · linarith only [h482, hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h0, hlam, p469_1]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h0, h466, h468, hc01, hc45, hlam, hphi, ht0b, ht5b, p469_1]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h0, h464, h466, h468, hc01, hc45, hlam, hphi, ht0b, ht5b, p469_1]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    rcases p469_3 (m.d 0 2) (by simp) with h491 | h491
                    · rcases p469_3 (m.d 1 2) (by simp) with h492 | h492
                      · rcases p469_3 (m.d 2 3) (by simp) with h493 | h493
                        · linarith only [h10, h493, hlam]
                        · linarith only [h466, h493, hlam]
                      · linarith only [h492, hlam, p469_0]
                    · linarith only [h491, h6, hlam]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h4, hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h10, hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h464, hlam, p469_1]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h0, h10, hc01, hc25, hlam, hphi, ht0b, ht5b, p469_1]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h5, hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h11, hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p469_1]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h0, h11, h466, h468, hc01, hc45, hlam, hphi, ht0b, ht5b, p469_1]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h6, hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h12, hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h466, hlam, p469_0]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [h467, hlam, p469_1]
                  · have p469_0 := h469c.1
                    have p469_1 := h469c.2.1
                    have p469_2 := h469c.2.2.1
                    have p469_3 := h469c.2.2.2
                    linarith only [hlam, p469_0]
                · linarith only [h13, h462, h468, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
              · linarith only [h0, h13, h4, h462, h463, h464, h466, h467, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h13, h4, h462, h466, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h13, h462, h463, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h517 | h517
        · rcases m.htr 2 3 4 (by decide) (by decide) with h518 | h518
          · linarith only [h10, h13, h518, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h520 | h520
            · linarith only [h10, h462, h520, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h522 | h522
              · rcases m.htr 3 4 5 (by decide) (by decide) with h523 | h523
                · rcases h2bigk with h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c | h524c
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h0, h11, h522, hc01, hc45, hlam, hphi, ht0b, ht5b, p524_1]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    rcases p524_3 (m.d 0 2) (by simp) with h527 | h527
                    · rcases p524_3 (m.d 1 2) (by simp) with h528 | h528
                      · linarith only [h0, h528, hlam]
                      · linarith only [h10, h528, hlam]
                    · linarith only [h527, hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    rcases p524_3 (m.d 0 2) (by simp) with h532 | h532
                    · rcases p524_3 (m.d 1 2) (by simp) with h533 | h533
                      · linarith only [h0, h533, hlam]
                      · linarith only [h11, h533, hlam]
                    · linarith only [h532, hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    rcases p524_3 (m.d 0 2) (by simp) with h537 | h537
                    · rcases p524_3 (m.d 1 2) (by simp) with h538 | h538
                      · linarith only [h0, h538, hlam]
                      · linarith only [h12, h538, hlam]
                    · linarith only [h537, hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h0, hlam, p524_1]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    rcases p524_3 (m.d 0 2) (by simp) with h544 | h544
                    · rcases p524_3 (m.d 1 2) (by simp) with h545 | h545
                      · rcases p524_3 (m.d 2 3) (by simp) with h546 | h546
                        · linarith only [h546, hlam, p524_0]
                        · rcases p524_3 (m.d 2 4) (by simp) with h548 | h548
                          · linarith only [h11, h548, hlam]
                          · linarith only [h518, h548, hlam]
                      · linarith only [h545, hlam, p524_0]
                    · linarith only [h4, h544, hlam]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h0, h522, hc01, hc45, hlam, hphi, ht0b, ht5b, p524_1]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    rcases p524_3 (m.d 0 2) (by simp) with h554 | h554
                    · rcases p524_3 (m.d 1 2) (by simp) with h555 | h555
                      · rcases p524_3 (m.d 2 3) (by simp) with h556 | h556
                        · linarith only [h10, h556, hlam]
                        · rcases p524_3 (m.d 2 4) (by simp) with h558 | h558
                          · linarith only [h11, h558, hlam]
                          · linarith only [h522, h558, hlam]
                      · linarith only [h555, hlam, p524_0]
                    · linarith only [h554, h6, hlam]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h4, hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h10, hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h518, hlam, p524_1]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h520, hlam, p524_1]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h5, hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h11, hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p524_1]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h0, h11, hc01, hc25, hlam, hphi, ht0b, ht5b, p524_1]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h6, hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h12, hlam, p524_0]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p524_1]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [h522, hlam, p524_1]
                  · have p524_0 := h524c.1
                    have p524_1 := h524c.2.1
                    have p524_2 := h524c.2.2.1
                    have p524_3 := h524c.2.2.2
                    linarith only [hlam, p524_0]
                · linarith only [h13, h523, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h579 | h579
                · rcases h2bigk with h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c | h580c
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h0, h11, h517, h522, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p580_1]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h13, h4, h517, h518, h522, h7, hlam, p580_2]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h13, h4, h517, h522, h7, hlam, p580_2]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    rcases p580_3 (m.d 0 2) (by simp) with h585 | h585
                    · rcases p580_3 (m.d 1 2) (by simp) with h586 | h586
                      · linarith only [h0, h586, hlam]
                      · linarith only [h12, h586, hlam]
                    · linarith only [h585, hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h0, hlam, p580_1]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    rcases p580_3 (m.d 0 2) (by simp) with h592 | h592
                    · rcases p580_3 (m.d 1 2) (by simp) with h593 | h593
                      · rcases p580_3 (m.d 2 3) (by simp) with h594 | h594
                        · linarith only [h594, hlam, p580_0]
                        · rcases p580_3 (m.d 2 4) (by simp) with h596 | h596
                          · linarith only [h11, h596, hlam]
                          · linarith only [h518, h596, hlam]
                      · linarith only [h593, hlam, p580_0]
                    · linarith only [h4, h592, hlam]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    rcases p580_3 (m.d 0 2) (by simp) with h601 | h601
                    · rcases p580_3 (m.d 1 2) (by simp) with h602 | h602
                      · rcases p580_3 (m.d 2 3) (by simp) with h603 | h603
                        · linarith only [h10, h603, hlam]
                        · rcases p580_3 (m.d 2 4) (by simp) with h605 | h605
                          · linarith only [h605, hlam, p580_0]
                          · rcases p580_3 (m.d 2 5) (by simp) with h607 | h607
                            · linarith only [h12, h607, hlam]
                            · linarith only [h522, h607, hlam]
                      · linarith only [h602, hlam, p580_0]
                    · linarith only [h5, h601, hlam]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    rcases p580_3 (m.d 0 2) (by simp) with h612 | h612
                    · rcases p580_3 (m.d 1 2) (by simp) with h613 | h613
                      · rcases p580_3 (m.d 2 3) (by simp) with h614 | h614
                        · linarith only [h10, h614, hlam]
                        · rcases p580_3 (m.d 2 4) (by simp) with h616 | h616
                          · linarith only [h11, h616, hlam]
                          · rcases p580_3 (m.d 2 5) (by simp) with h618 | h618
                            · linarith only [h618, hlam, p580_0]
                            · rcases h2emax with h620 | h620 | h620 | h620 | h620
                              · linarith only [h13, h4, h517, h518, h522, h620, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                              · linarith only [h620, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p580_1]
                              · rcases h4bigk with h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c | h623c
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h0, h4, h517, h518, h522, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p623_1]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  rcases p623_3 (m.d 0 4) (by simp) with h626 | h626
                                  · rcases p623_3 (m.d 1 4) (by simp) with h627 | h627
                                    · linarith only [h2, h627, hlam]
                                    · linarith only [h11, h627, hlam]
                                  · linarith only [h5, h626, hlam]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h462, h579, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p623_1, u1ehi2]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  rcases p623_3 (m.d 0 4) (by simp) with h632 | h632
                                  · rcases p623_3 (m.d 1 4) (by simp) with h633 | h633
                                    · linarith only [h2, h633, hlam]
                                    · linarith only [h517, h633, hlam]
                                  · linarith only [h632, hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h2, hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  rcases p623_3 (m.d 0 4) (by simp) with h639 | h639
                                  · rcases p623_3 (m.d 1 4) (by simp) with h640 | h640
                                    · rcases p623_3 (m.d 2 4) (by simp) with h641 | h641
                                      · linarith only [h11, h641, hlam]
                                      · rcases p623_3 (m.d 3 4) (by simp) with h643 | h643
                                        · rcases p623_3 (m.d 4 5) (by simp) with h644 | h644
                                          · linarith only [h517, h644, hlam]
                                          · linarith only [h522, h644, hlam]
                                        · linarith only [h518, h643, hlam]
                                    · linarith only [h11, h640, hlam]
                                  · linarith only [h5, h639, hlam]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h13, hlam, p623_1]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h0, h11, h518, h522, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p623_1]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h5, hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h11, hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h518, hlam, p623_1]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h522, hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h7, hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [hc34, hlam, hphi, ht12, ht23, p623_1, u1ehi3]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  rcases p623_3 (m.d 0 4) (by simp) with h659 | h659
                                  · rcases p623_3 (m.d 1 4) (by simp) with h660 | h660
                                    · linarith only [h13, h660, hlam]
                                    · linarith only [h11, h660, hlam]
                                  · linarith only [h5, h659, hlam]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h0, h4, h518, h522, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p623_1]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h9, hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h517, hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h2, h517, h518, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p623_1]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [h579, hlam, p623_0]
                                · have p623_0 := h623c.1
                                  have p623_1 := h623c.2.1
                                  have p623_2 := h623c.2.2.1
                                  have p623_3 := h623c.2.2.2
                                  linarith only [hlam, p623_0]
                              · rcases h4bigk with h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c | h671c
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h0, h4, h517, h518, h522, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  rcases p671_3 (m.d 0 4) (by simp) with h674 | h674
                                  · rcases p671_3 (m.d 1 4) (by simp) with h675 | h675
                                    · linarith only [h2, h675, hlam]
                                    · linarith only [h11, h675, hlam]
                                  · linarith only [h5, h674, hlam]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h13, h517, h522, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  rcases p671_3 (m.d 0 4) (by simp) with h680 | h680
                                  · rcases p671_3 (m.d 1 4) (by simp) with h681 | h681
                                    · linarith only [h2, h681, hlam]
                                    · linarith only [h517, h681, hlam]
                                  · linarith only [h680, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h2, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  rcases p671_3 (m.d 0 4) (by simp) with h687 | h687
                                  · rcases p671_3 (m.d 1 4) (by simp) with h688 | h688
                                    · rcases p671_3 (m.d 2 4) (by simp) with h689 | h689
                                      · linarith only [h11, h689, hlam]
                                      · rcases p671_3 (m.d 3 4) (by simp) with h691 | h691
                                        · rcases p671_3 (m.d 4 5) (by simp) with h692 | h692
                                          · linarith only [h517, h692, hlam]
                                          · linarith only [h522, h692, hlam]
                                        · linarith only [h518, h691, hlam]
                                    · linarith only [h11, h688, hlam]
                                  · linarith only [h5, h687, hlam]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h13, hlam, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h2, h518, h522, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h5, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h11, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h518, hlam, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h522, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h7, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [hc34, hlam, hphi, ht12, ht23, p671_1, u1ehi3]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  rcases p671_3 (m.d 0 4) (by simp) with h707 | h707
                                  · rcases p671_3 (m.d 1 4) (by simp) with h708 | h708
                                    · linarith only [h13, h708, hlam]
                                    · linarith only [h11, h708, hlam]
                                  · linarith only [h5, h707, hlam]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h0, h4, h518, h522, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h9, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h517, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h2, h517, h518, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p671_1]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [h579, hlam, p671_0]
                                · have p671_0 := h671c.1
                                  have p671_1 := h671c.2.1
                                  have p671_2 := h671c.2.2.1
                                  have p671_3 := h671c.2.2.2
                                  linarith only [hlam, p671_0]
                              · rcases h4bigk with h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h0, h4, h517, h518, h522, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  rcases p719_3 (m.d 0 4) (by simp) with h722 | h722
                                  · rcases p719_3 (m.d 1 4) (by simp) with h723 | h723
                                    · linarith only [h2, h723, hlam]
                                    · linarith only [h11, h723, hlam]
                                  · linarith only [h5, h722, hlam]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h13, h517, h522, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  rcases p719_3 (m.d 0 4) (by simp) with h728 | h728
                                  · rcases p719_3 (m.d 1 4) (by simp) with h729 | h729
                                    · linarith only [h2, h729, hlam]
                                    · linarith only [h517, h729, hlam]
                                  · linarith only [h728, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h2, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  rcases p719_3 (m.d 0 4) (by simp) with h735 | h735
                                  · rcases p719_3 (m.d 1 4) (by simp) with h736 | h736
                                    · rcases p719_3 (m.d 2 4) (by simp) with h737 | h737
                                      · linarith only [h11, h737, hlam]
                                      · rcases p719_3 (m.d 3 4) (by simp) with h739 | h739
                                        · rcases p719_3 (m.d 4 5) (by simp) with h740 | h740
                                          · linarith only [h517, h740, hlam]
                                          · linarith only [h522, h740, hlam]
                                        · linarith only [h518, h739, hlam]
                                    · linarith only [h11, h736, hlam]
                                  · linarith only [h5, h735, hlam]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h13, hlam, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h2, h518, h522, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h5, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h11, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h518, hlam, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h522, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h7, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [hc34, hlam, hphi, ht12, ht23, p719_1, u1ehi3]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  rcases p719_3 (m.d 0 4) (by simp) with h755 | h755
                                  · rcases p719_3 (m.d 1 4) (by simp) with h756 | h756
                                    · linarith only [h13, h756, hlam]
                                    · linarith only [h11, h756, hlam]
                                  · linarith only [h5, h755, hlam]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h0, h4, h518, h522, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h9, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h517, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h2, h517, h518, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p719_1]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [h579, hlam, p719_0]
                                · have p719_0 := h719c.1
                                  have p719_1 := h719c.2.1
                                  have p719_2 := h719c.2.2.1
                                  have p719_3 := h719c.2.2.2
                                  linarith only [hlam, p719_0]
                      · linarith only [h613, hlam, p580_0]
                    · linarith only [h6, h612, hlam]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h4, hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h10, hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h518, hlam, p580_1]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h520, hlam, p580_1]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h5, hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h11, hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p580_1]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h522, hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h6, hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h12, hlam, p580_0]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p580_1]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [h0, h12, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p580_1]
                  · have p580_0 := h580c.1
                    have p580_1 := h580c.2.1
                    have p580_2 := h580c.2.2.1
                    have p580_3 := h580c.2.2.2
                    linarith only [hlam, p580_0]
                · linarith only [h13, h517, h579, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h785 | h785
          · linarith only [h13, h785, hc23, hlam, hphi, ht12, u1ehi2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h787 | h787
            · linarith only [h462, h787, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h789 | h789
              · linarith only [h11, h517, h789, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h791 | h791
                · linarith only [h517, h791, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                · linarith only [h0, h13, h4, h7, h791, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h794 | h794
    · rcases m.htr 1 3 5 (by decide) (by decide) with h795 | h795
      · linarith only [h10, h12, h795, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h797 | h797
        · linarith only [h10, h12, h794, h797, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h799 | h799
          · linarith only [h0, h10, h12, h6, h799, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h794, h795, h799, hc23, hc35, hlam, hphi]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h802 | h802
      · linarith only [h11, h12, h794, h802, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h804 | h804
        · linarith only [h11, h12, h804, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h806 | h806
          · linarith only [h794, h806, hc23, hlam, hphi, ht12, u1ehi2]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h808 | h808
            · linarith only [h802, h808, hc23, hlam, hphi, ht12, u1ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h810 | h810
              · linarith only [h0, h11, h12, h4, h8, h808, h810, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h812 | h812
                · linarith only [h11, h12, h794, h810, h812, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                · linarith only [h0, h4, h7, h794, h812, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]

end R2N4
