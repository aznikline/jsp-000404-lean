import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_R_L_R_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h4, h7, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · rcases h3bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h2, h4, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h2, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11_1, u2ehi3]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      rcases p11_3 (m.d 0 3) (by simp) with h15 | h15
                      · rcases p11_3 (m.d 1 3) (by simp) with h16 | h16
                        · linarith only [h1, h16, hlam]
                        · linarith only [h16, h5, hlam]
                      · linarith only [h15, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      rcases p11_3 (m.d 0 3) (by simp) with h20 | h20
                      · rcases p11_3 (m.d 1 3) (by simp) with h21 | h21
                        · linarith only [h1, h21, hlam]
                        · linarith only [h21, h6, hlam]
                      · linarith only [h20, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h1, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h7, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u2ehi3]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h2, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h4, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h3, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h5, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h7, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h9, hlam, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h6, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h8, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                · linarith only [h0, h4, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h0, h4, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
              · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                · linarith only [h0, h4, h48, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                  · linarith only [h0, h4, h47, h50, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · rcases h3bigk with h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h4, h47, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p52_1]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p52_1, u2ehi2]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      rcases p52_3 (m.d 0 3) (by simp) with h56 | h56
                      · rcases p52_3 (m.d 1 3) (by simp) with h57 | h57
                        · linarith only [h1, h57, hlam]
                        · linarith only [h5, h57, hlam]
                      · linarith only [h56, hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h0, h2, h4, h47, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p52_1, u2ehi3]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h1, hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h47, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p52_1, u2ehi3]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h50, h6, hc34, hc45, hlam, hphi, p52_1]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h6, hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h2, hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h4, hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h0, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p52_1]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h48, hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h3, hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h5, hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h47, hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [hlam, p52_0]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h50, hlam, p52_1]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h50, hc03, hc45, hlam, hphi, ht34, p52_1]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h50, hc13, hc45, hlam, hphi, ht34, p52_1]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h50, hc23, hc45, hlam, hphi, ht34, p52_1]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [h50, hc34, hc45, hlam, hphi, p52_1]
                    · have p52_0 := h52c.1
                      have p52_1 := h52c.2.1
                      have p52_2 := h52c.2.2.1
                      have p52_3 := h52c.2.2.2
                      linarith only [hlam, p52_0]
              · linarith only [h1, h47, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
            · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
              · linarith only [h4, h5, h84, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
                · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                  · rcases h3bigk with h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h4, h86, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p88_1, u2ehi4]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h0, h2, h86, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p88_1, u2ehi4]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h0, h2, h4, h5, h86, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p88_1, u2ehi4]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      rcases p88_3 (m.d 0 3) (by simp) with h93 | h93
                      · rcases p88_3 (m.d 1 3) (by simp) with h94 | h94
                        · linarith only [h1, h94, hlam]
                        · linarith only [h83, h94, hlam]
                      · linarith only [h93, hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h1, hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h3, h5, h86, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p88_1, u2ehi4]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h5, hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h0, h2, h3, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p88_1]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h2, hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h4, hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h84, hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h0, h2, h87, hc01, hc45, hlam, hphi, ht0b, ht5b, p88_1]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h3, hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h0, h2, h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h0, h2, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h0, h2, h3, h87, hc01, hc45, hlam, hphi, ht0b, ht5b, p88_1]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p88_1]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h83, hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h86, hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [h87, hlam, p88_0]
                    · have p88_0 := h88c.1
                      have p88_1 := h88c.2.1
                      have p88_2 := h88c.2.2.1
                      have p88_3 := h88c.2.2.2
                      linarith only [hlam, p88_0]
                  · linarith only [h4, h5, h86, h87, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                · linarith only [h0, h2, h3, h5, h83, h86, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
              · linarith only [h0, h120, h4, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h122 | h122
                · linarith only [h122, h4, h83, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                  · rcases h3bigk with h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c | h125c
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h2, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi2]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi2]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h0, h124, h2, h4, h83, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi2]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h0, h2, h4, h83, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi2]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h1, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h124, h3, h83, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi2]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h5, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h83, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h2, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h4, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h120, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h122, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h3, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h0, h2, h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p125_1]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h0, h2, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p125_1, u2ehi2]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h0, h2, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p125_1]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p125_1]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h4, hc35, hlam, hphi, ht23, p125_1, u2ehi2]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hc35, hlam, hphi, ht23, p125_1, u2ehi2]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [h124, hlam, p125_0]
                    · have p125_0 := h125c.1
                      have p125_1 := h125c.2.1
                      have p125_2 := h125c.2.2.1
                      have p125_3 := h125c.2.2.2
                      linarith only [hlam, p125_0]
                  · linarith only [h124, h4, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
          · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
            · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
              · rcases m.htr 2 3 5 (by decide) (by decide) with h155 | h155
                · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                  · rcases h3bigk with h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h152, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p157_1]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h0, h152, h156, h2, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p157_1]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h0, h156, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p157_1]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      rcases p157_3 (m.d 0 3) (by simp) with h162 | h162
                      · rcases p157_3 (m.d 1 3) (by simp) with h163 | h163
                        · linarith only [h1, h163, hlam]
                        · linarith only [h153, h163, hlam]
                      · linarith only [h162, hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h1, hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h4, hlam, p157_1]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h156, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p157_1]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p157_1]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h2, hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h0, h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p157_1]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h0, h156, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p157_1]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h0, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p157_1]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h3, hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h152, hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h154, hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h152, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p157_1]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p157_1]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h153, hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h155, hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [h156, hlam, p157_0]
                    · have p157_0 := h157c.1
                      have p157_1 := h157c.2.1
                      have p157_2 := h157c.2.2.1
                      have p157_3 := h157c.2.2.2
                      linarith only [hlam, p157_0]
                  · rcases h3bigk with h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h153, h156, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p187_1, u2ehi2]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      rcases p187_3 (m.d 0 3) (by simp) with h191 | h191
                      · rcases p187_3 (m.d 1 3) (by simp) with h192 | h192
                        · linarith only [h1, h192, hlam]
                        · linarith only [h152, h192, hlam]
                      · linarith only [h191, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      rcases p187_3 (m.d 0 3) (by simp) with h196 | h196
                      · rcases p187_3 (m.d 1 3) (by simp) with h197 | h197
                        · linarith only [h1, h197, hlam]
                        · linarith only [h153, h197, hlam]
                      · linarith only [h196, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h1, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h4, hlam, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h1, h156, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h2, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h0, h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h0, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h0, h156, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h3, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h152, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h154, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h156, hlam, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h153, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h155, hlam, p187_0]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [h0, h153, h2, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p187_1]
                    · have p187_0 := h187c.1
                      have p187_1 := h187c.2.1
                      have p187_2 := h187c.2.2.1
                      have p187_3 := h187c.2.2.2
                      linarith only [hlam, p187_0]
                · linarith only [h153, h155, h4, hlam]
              · linarith only [h0, h154, h2, h3, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h223 | h223
              · rcases m.htr 2 3 5 (by decide) (by decide) with h224 | h224
                · linarith only [h0, h152, h153, h2, h224, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h224, h4, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h223, h4, hc34, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h228 | h228
            · rcases m.htr 2 3 4 (by decide) (by decide) with h229 | h229
              · linarith only [h0, h152, h2, h229, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · linarith only [h229, h4, hc34, hlam, hphi, ht23, u2ehi1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
              · linarith only [h0, h152, h2, h232, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · linarith only [h232, h4, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
        · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
          · linarith only [h236, h3, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h238 | h238
            · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
              · linarith only [h0, h235, h239, h3, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                · rcases m.htr 3 4 5 (by decide) (by decide) with h242 | h242
                  · rcases h3bigk with h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h235, h241, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p243_1, u2ehi4]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h241, h3, hc34, hlam, hphi, ht23, p243_1, u2ehi4]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h3, hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h242, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p243_1]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h1, hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h241, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p243_1, u2ehi4]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h236, hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h1, h242, h3, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p243_1]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h2, hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h235, hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h239, hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h0, h2, h242, hc01, hc45, hlam, hphi, ht0b, ht5b, p243_1]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [hc03, hc34, hlam, hphi, p243_1]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [hc13, hc34, hlam, hphi, p243_1]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [hc34, hlam, hphi, ht23, p243_1, u2ehi2]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      rcases p243_3 (m.d 0 3) (by simp) with h263 | h263
                      · linarith only [h263, h3, hlam]
                      · linarith only [h1, h238, h263, hc01, hlam, hphi, u0ehi2]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h241, hc23, hlam, hphi, ht01, ht12, p243_1, u0ehi2]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h238, hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h241, hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [h242, hlam, p243_0]
                    · have p243_0 := h243c.1
                      have p243_1 := h243c.2.1
                      have p243_2 := h243c.2.2.1
                      have p243_3 := h243c.2.2.2
                      linarith only [hlam, p243_0]
                  · linarith only [h1, h235, h241, h242, h3, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                · linarith only [h1, h238, h241, h3, hc23, hc34, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h273 | h273
              · linarith only [h273, h3, hc23, hlam, hphi, ht01, ht12, u0ehi2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h275 | h275
                · linarith only [h235, h238, h275, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h277 | h277
                  · rcases h3bigk with h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h235, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p278_1, u2ehi2]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h3, hc34, hlam, hphi, ht23, p278_1, u2ehi2]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h3, hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h235, h238, h3, hc34, hlam, hphi, ht23, p278_1, u2ehi2]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h1, hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p278_1, u2ehi2]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h236, hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h238, hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h2, hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h235, hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h273, hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h275, hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [hc03, hc34, hlam, hphi, p278_1]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [hc13, hc34, hlam, hphi, p278_1]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [hc34, hlam, hphi, ht23, p278_1, u2ehi2]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h235, h238, hc34, hlam, hphi, ht23, p278_1, u2ehi2]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p278_1]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h235, hc35, hlam, hphi, ht23, p278_1, u2ehi2]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [hc35, hlam, hphi, ht23, p278_1, u2ehi2]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [h277, hlam, p278_0]
                    · have p278_0 := h278c.1
                      have p278_1 := h278c.2.1
                      have p278_2 := h278c.2.2.1
                      have p278_3 := h278c.2.2.2
                      linarith only [hlam, p278_0]
                  · linarith only [h277, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
        · linarith only [h2, h235, h3, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h306 | h306
      · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
        · linarith only [h2, h307, hc12, hlam, hphi, ht01, u0ehi1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h309 | h309
          · rcases m.htr 1 3 5 (by decide) (by decide) with h310 | h310
            · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
              · rcases m.htr 2 3 5 (by decide) (by decide) with h312 | h312
                · rcases m.htr 3 4 5 (by decide) (by decide) with h313 | h313
                  · rcases h3bigk with h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c | h314c
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h309, h313, hc03, hc45, hlam, hphi, ht0b, ht5b, p314_1]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h2, hlam, p314_1]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h2, h313, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p314_1]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      rcases p314_3 (m.d 0 3) (by simp) with h319 | h319
                      · rcases p314_3 (m.d 1 3) (by simp) with h320 | h320
                        · linarith only [h1, h320, hlam]
                        · linarith only [h310, h320, hlam]
                      · linarith only [h319, hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h1, hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h307, hlam, p314_1]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h313, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p314_1]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p314_1]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [hc23, hlam, hphi, ht01, ht12, p314_1, u0ehi2]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h307, hc23, hlam, hphi, p314_1, u2ehi1]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h313, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p314_1]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      rcases p314_3 (m.d 0 3) (by simp) with h333 | h333
                      · linarith only [h2, h333, hlam]
                      · linarith only [h1, h310, h333, hlam]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h306, hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h309, hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h311, hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h1, h309, hc03, hc35, hlam, hphi, ht0b, ht5b, p314_1]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p314_1]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h310, hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h312, hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [h313, hlam, p314_0]
                    · have p314_0 := h314c.1
                      have p314_1 := h314c.2.1
                      have p314_2 := h314c.2.2.1
                      have p314_3 := h314c.2.2.2
                      linarith only [hlam, p314_0]
                  · rcases h3bigk with h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c | h346c
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h310, h313, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h2, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      rcases p346_3 (m.d 0 3) (by simp) with h350 | h350
                      · rcases p346_3 (m.d 1 3) (by simp) with h351 | h351
                        · linarith only [h1, h351, hlam]
                        · linarith only [h309, h351, hlam]
                      · linarith only [h350, hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      rcases p346_3 (m.d 0 3) (by simp) with h355 | h355
                      · rcases p346_3 (m.d 1 3) (by simp) with h356 | h356
                        · linarith only [h1, h356, hlam]
                        · linarith only [h310, h356, hlam]
                      · linarith only [h355, hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h1, hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h307, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h1, h313, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [hc23, hlam, hphi, ht01, ht12, p346_1, u0ehi2]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h307, hc23, hlam, hphi, p346_1, u2ehi1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      rcases p346_3 (m.d 0 3) (by simp) with h368 | h368
                      · linarith only [h2, h368, hlam]
                      · linarith only [h306, h368, hlam]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      rcases p346_3 (m.d 0 3) (by simp) with h371 | h371
                      · linarith only [h2, h371, hlam]
                      · linarith only [h1, h2, h310, h371, hc01, hlam, hphi, u0ehi1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h306, hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h309, hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h311, hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h313, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h1, h310, hlam, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h310, hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h312, hlam, p346_0]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [h1, h310, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p346_1]
                    · have p346_0 := h346c.1
                      have p346_1 := h346c.2.1
                      have p346_2 := h346c.2.2.1
                      have p346_3 := h346c.2.2.2
                      linarith only [hlam, p346_0]
                · linarith only [h1, h310, h312, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h2, h311, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
              · rcases m.htr 2 3 5 (by decide) (by decide) with h387 | h387
                · linarith only [h307, h310, h387, hc23, hlam, hphi, u2ehi1]
                · linarith only [h2, h387, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
              · linarith only [h2, h309, h386, hc13, hlam, hphi, ht01, u0ehi1]
          · linarith only [h2, h306, h307, h309, hc23, hlam, hphi, u2ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h392 | h392
        · linarith only [h2, h392, hc12, hlam, hphi, ht01, u0ehi1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h394 | h394
          · linarith only [h306, h394, hc13, hlam, hphi, ht01, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h396 | h396
            · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
              · linarith only [h2, h306, h397, hc23, hlam, hphi, ht01, ht12, u0ehi1]
              · linarith only [h2, h397, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h400 | h400
              · linarith only [h2, h306, h400, hc23, hlam, hphi, ht01, ht12, u0ehi1]
              · linarith only [h2, h400, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h403 | h403
    · linarith only [h0, h1, h403, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h405 | h405
      · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
        · linarith only [h0, h1, h403, h406, hc13, hlam, hphi, ht01, u0ehi1]
        · linarith only [h0, h1, h406, hc23, hlam, hphi, u2ehi1]
      · linarith only [h0, h1, h405, hc34, hlam, hphi, ht23, u2ehi1]

end R2N4
