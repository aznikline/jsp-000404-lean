import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S7
import Jsp000404.R1LeavesN7_21S8
import Jsp000404.R1LeavesN7_21S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6287 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h6934 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 3 5 (by decide) (by decide) with h7149 | h7149
  · rcases m.htr 0 4 5 (by decide) (by decide) with h7150 | h7150
    · rcases m.htr 1 2 3 (by decide) (by decide) with h7151 | h7151
      · rcases m.htr 1 2 4 (by decide) (by decide) with h7152 | h7152
        · rcases m.htr 1 2 5 (by decide) (by decide) with h7153 | h7153
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7154 | h7154
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7155 | h7155
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7156 | h7156
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7157 | h7157
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7158 | h7158
                    · rcases h2bigk with h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c | h7159c
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [hlam, p7159_0]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h0, hlam, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h4553, hlam, p7159_0]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h6287, hlam, p7159_0]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h6934, hlam, p7159_0]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        rcases p7159_3 (m.d 0 2) (by simp) with h7165 | h7165
                        · linarith only [h0, h7165, hlam]
                        · rcases p7159_3 (m.d 1 2) (by simp) with h7167 | h7167
                          · rcases p7159_3 (m.d 2 3) (by simp) with h7168 | h7168
                            · linarith only [h7151, h7168, hlam]
                            · linarith only [h4553, h7168, hlam]
                          · linarith only [h0, h7167, hlam]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [hlam, p7159_0]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h7155, h7158, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h0, h6934, h7157, hc01, hc12, hlam, hphi, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h0, h6934, hc01, hc12, hlam, hphi, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h0, h7151, hc01, hc12, hlam, hphi, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h7151, hlam, p7159_0]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [hlam, p7159_0]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h0, h6934, h7151, h7157, hc01, hc12, hlam, hphi, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h0, h6934, h7151, hc01, hc12, hlam, hphi, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h0, h7152, hc01, hc12, hlam, hphi, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h7152, hlam, p7159_0]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h7155, hlam, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [hlam, p7159_0]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h0, h6934, h7151, h7155, hc01, hc12, hlam, hphi, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h0, h7153, hc01, hc12, hlam, hphi, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h7153, hlam, p7159_0]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h7156, hlam, p7159_1]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [h7157, hlam, p7159_0]
                      · have p7159_0 := h7159c.1
                        have p7159_1 := h7159c.2.1
                        have p7159_2 := h7159c.2.2.1
                        have p7159_3 := h7159c.2.2.2
                        linarith only [hlam, p7159_0]
                    · rcases h2bigk with h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c | h7191c
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [hlam, p7191_0]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h0, hlam, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h4553, hlam, p7191_0]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h6287, hlam, p7191_0]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h6934, hlam, p7191_0]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        rcases p7191_3 (m.d 0 2) (by simp) with h7197 | h7197
                        · linarith only [h0, h7197, hlam]
                        · rcases p7191_3 (m.d 1 2) (by simp) with h7199 | h7199
                          · rcases p7191_3 (m.d 2 3) (by simp) with h7200 | h7200
                            · linarith only [h7151, h7200, hlam]
                            · linarith only [h4553, h7200, hlam]
                          · linarith only [h0, h7199, hlam]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [hlam, p7191_0]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h0, h4553, hc01, hc12, hlam, hphi, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h6287, h7150, h7158, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h0, h6934, hc01, hc12, hlam, hphi, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h0, h7151, hc01, hc12, hlam, hphi, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h7151, hlam, p7191_0]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [hlam, p7191_0]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h6287, h7150, h7151, h7158, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h0, h6934, h7151, hc01, hc12, hlam, hphi, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h0, h7152, hc01, hc12, hlam, hphi, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h7152, hlam, p7191_0]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h7155, hlam, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [hlam, p7191_0]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h0, h6934, h7151, h7155, hc01, hc12, hlam, hphi, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h0, h7153, hc01, hc12, hlam, hphi, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h7153, hlam, p7191_0]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h7156, hlam, p7191_1]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [h7157, hlam, p7191_0]
                      · have p7191_0 := h7191c.1
                        have p7191_1 := h7191c.2.1
                        have p7191_2 := h7191c.2.2.1
                        have p7191_3 := h7191c.2.2.2
                        linarith only [hlam, p7191_0]
                  · linarith only [h0, h6287, h7150, h7157, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h4553, h7149, h7156, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7225 | h7225
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7226 | h7226
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7227 | h7227
                    · rcases h2bigk with h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c | h7228c
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h0, hlam, p7228_1]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h4553, hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h6287, hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h6934, hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        rcases p7228_3 (m.d 0 2) (by simp) with h7234 | h7234
                        · linarith only [h0, h7234, hlam]
                        · rcases p7228_3 (m.d 1 2) (by simp) with h7236 | h7236
                          · rcases p7228_3 (m.d 2 3) (by simp) with h7237 | h7237
                            · linarith only [h7151, h7237, hlam]
                            · linarith only [h4553, h7237, hlam]
                          · linarith only [h0, h7236, hlam]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h0, h4553, hc01, hc12, hlam, hphi, p7228_1]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h0, h6934, h7155, h7225, hc01, hc12, hlam, hphi, p7228_1]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h0, h6934, hc01, hc12, hlam, hphi, p7228_1]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h0, h7155, hc01, hc34, hlam, hphi, ht12, ht23, p7228_1]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h7151, hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h7155, hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h0, h6934, h7155, hc01, hc34, hlam, hphi, ht12, ht23, p7228_1]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h0, h7152, hc01, hc12, hlam, hphi, p7228_1]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h7152, hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h4553, h7149, h7152, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7228_1]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h0, h6934, h7152, hc01, hc12, hlam, hphi, p7228_1]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h0, h7155, h7225, hc01, hc34, hlam, hphi, ht12, ht23, p7228_1]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h7153, hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h7225, hlam, p7228_1]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [h7226, hlam, p7228_0]
                      · have p7228_0 := h7228c.1
                        have p7228_1 := h7228c.2.1
                        have p7228_2 := h7228c.2.2.1
                        have p7228_3 := h7228c.2.2.2
                        linarith only [hlam, p7228_0]
                    · linarith only [h0, h4553, h7155, h7227, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h4553, h6287, h7149, h7150, h7155, h7226, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h4553, h7149, h7225, hlam]
            · linarith only [h0, h6287, h7150, h7152, h7154, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
          · linarith only [h0, h4553, h7151, h7153, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h4553, h7151, h7152, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h7266 | h7266
        · linarith only [h0, h6287, h7151, h7266, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h7268 | h7268
          · linarith only [h0, h6934, h7151, h7268, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7270 | h7270
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7271 | h7271
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7272 | h7272
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7273 | h7273
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7274 | h7274
                    · rcases h2bigk with h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c | h7275c
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [hlam, p7275_0]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h0, hlam, p7275_1]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h4553, hlam, p7275_0]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h6287, hlam, p7275_0]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h6934, hlam, p7275_0]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h0, h7268, h7271, h7273, hc01, hc23, hlam, hphi, ht12, p7275_1]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [hlam, p7275_0]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h7151, hlam, p7275_0]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h7266, hlam, p7275_0]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h7268, hlam, p7275_0]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        rcases p7275_3 (m.d 0 2) (by simp) with h7286 | h7286
                        · linarith only [h7286, hlam, p7275_0]
                        · rcases p7275_3 (m.d 1 2) (by simp) with h7288 | h7288
                          · linarith only [h7151, h7288, hlam]
                          · linarith only [h0, h7288, hlam]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7275_1]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [hlam, p7275_0]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h0, h6287, hc01, hc23, hlam, hphi, ht12, p7275_1]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h0, h7268, hc01, hc23, hlam, hphi, ht12, p7275_1]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        rcases p7275_3 (m.d 0 2) (by simp) with h7295 | h7295
                        · linarith only [h7295, hlam, p7275_0]
                        · rcases p7275_3 (m.d 1 2) (by simp) with h7297 | h7297
                          · linarith only [h7266, h7297, hlam]
                          · linarith only [h0, h7297, hlam]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7275_1]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h7271, hlam, p7275_1]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [hlam, p7275_0]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h0, h7268, h7271, hc01, hc23, hlam, hphi, ht12, p7275_1]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        rcases p7275_3 (m.d 0 2) (by simp) with h7304 | h7304
                        · linarith only [h7304, hlam, p7275_0]
                        · rcases p7275_3 (m.d 1 2) (by simp) with h7306 | h7306
                          · linarith only [h7268, h7306, hlam]
                          · linarith only [h0, h7306, hlam]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p7275_1]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h7272, hlam, p7275_1]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [h7273, hlam, p7275_0]
                      · have p7275_0 := h7275c.1
                        have p7275_1 := h7275c.2.1
                        have p7275_2 := h7275c.2.2.1
                        have p7275_3 := h7275c.2.2.2
                        linarith only [hlam, p7275_0]
                    · rcases h2bigk with h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c | h7313c
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [hlam, p7313_0]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h0, hlam, p7313_1]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h4553, hlam, p7313_0]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h6287, hlam, p7313_0]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h6934, hlam, p7313_0]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h0, h7151, hc01, hc23, hlam, hphi, ht12, p7313_1]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [hlam, p7313_0]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h7151, hlam, p7313_0]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h7266, hlam, p7313_0]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h7268, hlam, p7313_0]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        rcases p7313_3 (m.d 0 2) (by simp) with h7324 | h7324
                        · linarith only [h7324, hlam, p7313_0]
                        · rcases p7313_3 (m.d 1 2) (by simp) with h7326 | h7326
                          · linarith only [h7151, h7326, hlam]
                          · linarith only [h0, h7326, hlam]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7313_1]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [hlam, p7313_0]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h0, h6287, hc01, hc23, hlam, hphi, ht12, p7313_1]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h0, h7268, hc01, hc23, hlam, hphi, ht12, p7313_1]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        rcases p7313_3 (m.d 0 2) (by simp) with h7333 | h7333
                        · linarith only [h7333, hlam, p7313_0]
                        · rcases p7313_3 (m.d 1 2) (by simp) with h7335 | h7335
                          · linarith only [h7266, h7335, hlam]
                          · linarith only [h0, h7335, hlam]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7313_1]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h7271, hlam, p7313_1]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [hlam, p7313_0]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h0, h7268, h7271, hc01, hc23, hlam, hphi, ht12, p7313_1]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        rcases p7313_3 (m.d 0 2) (by simp) with h7342 | h7342
                        · linarith only [h7342, hlam, p7313_0]
                        · rcases p7313_3 (m.d 1 2) (by simp) with h7344 | h7344
                          · linarith only [h7268, h7344, hlam]
                          · linarith only [h0, h7344, hlam]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p7313_1]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h7272, hlam, p7313_1]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [h7273, hlam, p7313_0]
                      · have p7313_0 := h7313c.1
                        have p7313_1 := h7313c.2.1
                        have p7313_2 := h7313c.2.2.1
                        have p7313_3 := h7313c.2.2.2
                        linarith only [hlam, p7313_0]
                  · linarith only [h6287, h7150, h7273, hlam]
                · linarith only [h4553, h7149, h7272, hlam]
              · linarith only [h0, h7151, h7271, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h7150, h7266, h7270, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h7355 | h7355
      · rcases m.htr 1 2 4 (by decide) (by decide) with h7356 | h7356
        · rcases m.htr 1 2 5 (by decide) (by decide) with h7357 | h7357
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7358 | h7358
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7359 | h7359
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7360 | h7360
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7361 | h7361
                  · linarith only [h0, h6287, h7150, h7356, h7361, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h6287, h7356, h7358, h7361, hc01, hc12, hlam, hphi]
                · linarith only [h4553, h7149, h7360, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7365 | h7365
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7366 | h7366
                  · linarith only [h0, h6287, h7150, h7356, h7366, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h6287, h7356, h7358, h7366, hc01, hc12, hlam, hphi]
                · linarith only [h4553, h7149, h7365, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7370 | h7370
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7371 | h7371
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7372 | h7372
                  · linarith only [h7356, h7358, h7372, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7374 | h7374
                    · linarith only [h0, h6287, h7150, h7355, h7370, h7374, hc01, hc13, hlam, hphi]
                    · rcases h2bigk with h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c | h7376c
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [hlam, p7376_0]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h0, hlam, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h4553, hlam, p7376_0]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h6287, hlam, p7376_0]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h6934, hlam, p7376_0]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        rcases p7376_3 (m.d 0 2) (by simp) with h7382 | h7382
                        · linarith only [h0, h7382, hlam]
                        · rcases p7376_3 (m.d 1 2) (by simp) with h7384 | h7384
                          · rcases p7376_3 (m.d 2 3) (by simp) with h7385 | h7385
                            · linarith only [h7355, h7385, hlam]
                            · linarith only [h4553, h7385, hlam]
                          · linarith only [h0, h7384, hlam]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [hlam, p7376_0]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h0, h4553, hc01, hc12, hlam, hphi, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h0, h6287, hc01, hc12, hlam, hphi, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h0, h6287, h7372, hc01, hc12, hlam, hphi, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h0, h7355, hc01, hc12, hlam, hphi, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h7355, hlam, p7376_0]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [hlam, p7376_0]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h0, h6287, h7355, hc01, hc12, hlam, hphi, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h0, h6287, h7355, h7372, hc01, hc12, hlam, hphi, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h0, h7356, h7358, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h7356, hlam, p7376_0]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h7370, hlam, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [hlam, p7376_0]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h7372, hlam, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h0, h7357, hc01, hc12, hlam, hphi, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h7357, hlam, p7376_0]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h7371, hlam, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [h0, h6287, h7355, h7371, hc01, hc12, hlam, hphi, p7376_1]
                      · have p7376_0 := h7376c.1
                        have p7376_1 := h7376c.2.1
                        have p7376_2 := h7376c.2.2.1
                        have p7376_3 := h7376c.2.2.2
                        linarith only [hlam, p7376_0]
                · linarith only [h4553, h7149, h7371, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7409 | h7409
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7410 | h7410
                  · linarith only [h7356, h7358, h7410, hlam]
                  · linarith only [h7370, h7409, h7410, hlam]
                · linarith only [h4553, h7149, h7409, hlam]
          · linarith only [h0, h4553, h7355, h7357, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h4553, h7355, h7356, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h7416 | h7416
        · linarith only [h0, h6287, h7355, h7416, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h7418 | h7418
          · linarith only [h0, h6934, h7355, h7418, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7420 | h7420
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7421 | h7421
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7422 | h7422
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7423 | h7423
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7424 | h7424
                    · linarith only [h0, h6287, h7150, h7421, h7424, hc01, hc23, hlam, hphi, ht12]
                    · rcases h2bigk with h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c | h7426c
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [hlam, p7426_0]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h0, hlam, p7426_1]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h4553, hlam, p7426_0]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h6287, hlam, p7426_0]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h6934, hlam, p7426_0]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h0, h7418, h7421, h7423, hc01, hc23, hlam, hphi, ht12, p7426_1]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [hlam, p7426_0]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h7355, hlam, p7426_0]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h7416, hlam, p7426_0]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h7418, hlam, p7426_0]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        rcases p7426_3 (m.d 0 2) (by simp) with h7437 | h7437
                        · linarith only [h7437, hlam, p7426_0]
                        · rcases p7426_3 (m.d 1 2) (by simp) with h7439 | h7439
                          · linarith only [h7355, h7439, hlam]
                          · linarith only [h0, h7439, hlam]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7426_1]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [hlam, p7426_0]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h0, h6287, hc01, hc23, hlam, hphi, ht12, p7426_1]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h0, h7418, hc01, hc23, hlam, hphi, ht12, p7426_1]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        rcases p7426_3 (m.d 0 2) (by simp) with h7446 | h7446
                        · linarith only [h7446, hlam, p7426_0]
                        · rcases p7426_3 (m.d 1 2) (by simp) with h7448 | h7448
                          · linarith only [h7416, h7448, hlam]
                          · linarith only [h0, h7448, hlam]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7426_1]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h7421, hlam, p7426_1]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [hlam, p7426_0]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h0, h7418, h7421, hc01, hc23, hlam, hphi, ht12, p7426_1]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        rcases p7426_3 (m.d 0 2) (by simp) with h7455 | h7455
                        · linarith only [h7455, hlam, p7426_0]
                        · rcases p7426_3 (m.d 1 2) (by simp) with h7457 | h7457
                          · linarith only [h7418, h7457, hlam]
                          · linarith only [h0, h7457, hlam]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p7426_1]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h7422, hlam, p7426_1]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [h7423, hlam, p7426_0]
                      · have p7426_0 := h7426c.1
                        have p7426_1 := h7426c.2.1
                        have p7426_2 := h7426c.2.2.1
                        have p7426_3 := h7426c.2.2.2
                        linarith only [hlam, p7426_0]
                  · linarith only [h0, h7416, h7423, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h4553, h7149, h7422, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h7355, h7421, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7467 | h7467
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7468 | h7468
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7469 | h7469
                  · linarith only [h0, h7416, h7420, h7467, h7469, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h7416, h7469, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h7149, h7467, h7468, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h0, h7355, h7467, hc01, hc34, hlam, hphi, ht12, ht23]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h7474 | h7474
    · rcases m.htr 1 2 3 (by decide) (by decide) with h7475 | h7475
      · rcases m.htr 1 2 4 (by decide) (by decide) with h7476 | h7476
        · rcases m.htr 1 2 5 (by decide) (by decide) with h7477 | h7477
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7478 | h7478
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7479 | h7479
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7480 | h7480
                · linarith only [h0, h4553, h7149, h7475, h7480, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7482 | h7482
                  · linarith only [h7479, h7480, h7482, hlam]
                  · linarith only [h6287, h7474, h7482, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7485 | h7485
                · linarith only [h0, h4553, h7149, h7479, h7485, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7487 | h7487
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7488 | h7488
                    · rcases h2bigk with h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c | h7489c
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h0, hlam, p7489_1]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h4553, hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h6287, hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h6934, hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        rcases p7489_3 (m.d 0 2) (by simp) with h7495 | h7495
                        · linarith only [h0, h7495, hlam]
                        · rcases p7489_3 (m.d 1 2) (by simp) with h7497 | h7497
                          · rcases p7489_3 (m.d 2 3) (by simp) with h7498 | h7498
                            · linarith only [h7475, h7498, hlam]
                            · linarith only [h4553, h7498, hlam]
                          · linarith only [h0, h7497, hlam]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h0, h4553, hc01, hc12, hlam, hphi, p7489_1]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h0, h6287, hc01, hc12, hlam, hphi, p7489_1]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h0, h6934, hc01, hc12, hlam, hphi, p7489_1]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h0, h7475, hc01, hc12, hlam, hphi, p7489_1]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h7475, hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h7479, hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h7485, hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h0, h7476, hc01, hc12, hlam, hphi, p7489_1]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h7476, hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h0, h4553, h7476, hc01, hc12, hlam, hphi, p7489_1]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h0, h4553, h7476, h7485, hc01, hc12, hlam, hphi, p7489_1]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h0, h7477, hc01, hc12, hlam, hphi, p7489_1]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h7477, hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h0, h4553, h7477, hc01, hc12, hlam, hphi, p7489_1]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [h7487, hlam, p7489_0]
                      · have p7489_0 := h7489c.1
                        have p7489_1 := h7489c.2.1
                        have p7489_2 := h7489c.2.2.1
                        have p7489_3 := h7489c.2.2.2
                        linarith only [hlam, p7489_0]
                    · linarith only [h0, h4553, h7474, h7479, h7488, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h6287, h7474, h7487, hlam]
            · linarith only [h6287, h7474, h7476, h7478, hlam]
          · linarith only [h0, h6287, h7476, h7477, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h4553, h7475, h7476, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h7526 | h7526
        · linarith only [h0, h6287, h7475, h7526, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h7528 | h7528
          · linarith only [h0, h6934, h7475, h7528, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7530 | h7530
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7531 | h7531
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7532 | h7532
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7533 | h7533
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7534 | h7534
                    · rcases h2bigk with h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c | h7535c
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [hlam, p7535_0]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h0, hlam, p7535_1]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h4553, hlam, p7535_0]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h6287, hlam, p7535_0]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h6934, hlam, p7535_0]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h0, h7528, h7531, h7533, hc01, hc23, hlam, hphi, ht12, p7535_1]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [hlam, p7535_0]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h7475, hlam, p7535_0]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h7526, hlam, p7535_0]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h7528, hlam, p7535_0]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        rcases p7535_3 (m.d 0 2) (by simp) with h7546 | h7546
                        · linarith only [h7546, hlam, p7535_0]
                        · rcases p7535_3 (m.d 1 2) (by simp) with h7548 | h7548
                          · linarith only [h7475, h7548, hlam]
                          · linarith only [h0, h7548, hlam]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7535_1]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [hlam, p7535_0]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h0, h6287, hc01, hc23, hlam, hphi, ht12, p7535_1]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h0, h7528, hc01, hc23, hlam, hphi, ht12, p7535_1]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        rcases p7535_3 (m.d 0 2) (by simp) with h7555 | h7555
                        · linarith only [h7555, hlam, p7535_0]
                        · rcases p7535_3 (m.d 1 2) (by simp) with h7557 | h7557
                          · linarith only [h7526, h7557, hlam]
                          · linarith only [h0, h7557, hlam]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7535_1]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h7531, hlam, p7535_1]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [hlam, p7535_0]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h0, h7528, h7531, hc01, hc23, hlam, hphi, ht12, p7535_1]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        rcases p7535_3 (m.d 0 2) (by simp) with h7564 | h7564
                        · linarith only [h7564, hlam, p7535_0]
                        · rcases p7535_3 (m.d 1 2) (by simp) with h7566 | h7566
                          · linarith only [h7528, h7566, hlam]
                          · linarith only [h0, h7566, hlam]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p7535_1]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h7532, hlam, p7535_1]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [h7533, hlam, p7535_0]
                      · have p7535_0 := h7535c.1
                        have p7535_1 := h7535c.2.1
                        have p7535_2 := h7535c.2.2.1
                        have p7535_3 := h7535c.2.2.2
                        linarith only [hlam, p7535_0]
                    · linarith only [h7149, h7474, h7534, hlam]
                  · linarith only [h2858, h7474, h7526, h7530, h7533, hlam]
                · linarith only [h0, h7475, h7532, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h0, h7475, h7531, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h7474, h7526, h7530, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h7578 | h7578
      · rcases m.htr 1 2 4 (by decide) (by decide) with h7579 | h7579
        · rcases m.htr 1 2 5 (by decide) (by decide) with h7580 | h7580
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7581 | h7581
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7582 | h7582
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7583 | h7583
                · linarith only [h0, h4553, h7149, h7578, h7583, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7585 | h7585
                  · linarith only [h0, h6287, h7474, h7578, h7582, h7585, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h6287, h7581, h7585, hc01, hc14, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7588 | h7588
                · linarith only [h0, h4553, h7149, h7582, h7588, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7590 | h7590
                  · linarith only [h0, h6287, h7474, h7579, h7590, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h6287, h7579, h7581, h7590, hc01, hc12, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7593 | h7593
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7594 | h7594
                · linarith only [h0, h4553, h7149, h7578, h7594, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7596 | h7596
                  · linarith only [h0, h6287, h7474, h7579, h7596, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7598 | h7598
                    · linarith only [h0, h6287, h7579, h7581, h7593, h7594, h7598, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases h2bigk with h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c | h7600c
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [hlam, p7600_0]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h0, hlam, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h4553, hlam, p7600_0]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h6287, hlam, p7600_0]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h6934, hlam, p7600_0]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        rcases p7600_3 (m.d 0 2) (by simp) with h7606 | h7606
                        · linarith only [h0, h7606, hlam]
                        · rcases p7600_3 (m.d 1 2) (by simp) with h7608 | h7608
                          · rcases p7600_3 (m.d 2 3) (by simp) with h7609 | h7609
                            · linarith only [h7578, h7609, hlam]
                            · linarith only [h4553, h7609, hlam]
                          · linarith only [h0, h7608, hlam]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [hlam, p7600_0]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h0, h4553, hc01, hc12, hlam, hphi, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h0, h6287, hc01, hc12, hlam, hphi, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h0, h6934, hc01, hc12, hlam, hphi, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h0, h7578, hc01, hc12, hlam, hphi, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h7578, hlam, p7600_0]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [hlam, p7600_0]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h0, h6287, h7578, hc01, hc12, hlam, hphi, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h7594, hlam, p7600_0]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h0, h7579, hc01, hc12, hlam, hphi, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h7579, hlam, p7600_0]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h7593, hlam, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [hlam, p7600_0]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h7596, hlam, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h0, h7580, hc01, hc12, hlam, hphi, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h7580, hlam, p7600_0]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h7580, h7593, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [h0, h6287, h7580, hc01, hc12, hlam, hphi, p7600_1]
                      · have p7600_0 := h7600c.1
                        have p7600_1 := h7600c.2.1
                        have p7600_2 := h7600c.2.2.1
                        have p7600_3 := h7600c.2.2.2
                        linarith only [hlam, p7600_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7632 | h7632
                · linarith only [h0, h4553, h7149, h7579, h7581, h7593, h7632, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7634 | h7634
                  · linarith only [h7579, h7581, h7634, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7636 | h7636
                    · linarith only [h0, h4553, h7579, h7581, h7593, h7636, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h4553, h7593, h7636, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h4553, h7578, h7580, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h4553, h7578, h7579, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h7641 | h7641
        · linarith only [h0, h6287, h7578, h7641, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h7643 | h7643
          · linarith only [h0, h6934, h7578, h7643, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7645 | h7645
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7646 | h7646
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7647 | h7647
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7648 | h7648
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7649 | h7649
                    · linarith only [h0, h6287, h7474, h7646, h7649, hc01, hc23, hlam, hphi, ht12]
                    · rcases h2bigk with h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c | h7651c
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [hlam, p7651_0]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h0, hlam, p7651_1]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h4553, hlam, p7651_0]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h6287, hlam, p7651_0]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h6934, hlam, p7651_0]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h0, h7643, h7646, h7648, hc01, hc23, hlam, hphi, ht12, p7651_1]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [hlam, p7651_0]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h7578, hlam, p7651_0]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h7641, hlam, p7651_0]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h7643, hlam, p7651_0]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        rcases p7651_3 (m.d 0 2) (by simp) with h7662 | h7662
                        · linarith only [h7662, hlam, p7651_0]
                        · rcases p7651_3 (m.d 1 2) (by simp) with h7664 | h7664
                          · linarith only [h7578, h7664, hlam]
                          · linarith only [h0, h7664, hlam]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p7651_1]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [hlam, p7651_0]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h0, h6287, hc01, hc23, hlam, hphi, ht12, p7651_1]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h0, h7643, hc01, hc23, hlam, hphi, ht12, p7651_1]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        rcases p7651_3 (m.d 0 2) (by simp) with h7671 | h7671
                        · linarith only [h7671, hlam, p7651_0]
                        · rcases p7651_3 (m.d 1 2) (by simp) with h7673 | h7673
                          · linarith only [h7641, h7673, hlam]
                          · linarith only [h0, h7673, hlam]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p7651_1]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h7646, hlam, p7651_1]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [hlam, p7651_0]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h0, h7643, h7646, hc01, hc23, hlam, hphi, ht12, p7651_1]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        rcases p7651_3 (m.d 0 2) (by simp) with h7680 | h7680
                        · linarith only [h7680, hlam, p7651_0]
                        · rcases p7651_3 (m.d 1 2) (by simp) with h7682 | h7682
                          · linarith only [h7643, h7682, hlam]
                          · linarith only [h0, h7682, hlam]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p7651_1]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h7647, hlam, p7651_1]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [h7648, hlam, p7651_0]
                      · have p7651_0 := h7651c.1
                        have p7651_1 := h7651c.2.1
                        have p7651_2 := h7651c.2.2.1
                        have p7651_3 := h7651c.2.2.2
                        linarith only [hlam, p7651_0]
                  · linarith only [h0, h6287, h7645, h7648, hc01, hc14, hlam, hphi]
                · linarith only [h0, h6287, h7474, h7641, h7645, h7646, h7647, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h0, h7578, h7646, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7692 | h7692
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7693 | h7693
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7694 | h7694
                  · linarith only [h0, h7641, h7645, h7694, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h7641, h7694, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h7578, h7693, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h0, h7578, h7692, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6287 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 2 5 (by decide) (by decide) with h6934 | h6934
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x1_x1_x0 m hb0 hb2 hb5 hg0 hg2858 h4553 h6287 h6934
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x1_x1_x1 m hb0 hb2 hb5 hg0 hg2858 h4553 h6287 h6934

set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 2 4 (by decide) (by decide) with h6287 | h6287
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x1_x0 m hb0 hb2 hb5 hg0 hg2858 h4553 h6287
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x1_x1 m hb0 hb2 hb5 hg0 hg2858 h4553 h6287

set_option maxHeartbeats 6292000 in
set_option maxHeartbeats 6292000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s2 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h2858 := hg2858
  rcases m.htr 0 2 3 (by decide) (by decide) with h4553 | h4553
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x0 m hb0 hb2 hb5 hg0 hg2858 h4553
  · exact r1l7_10_12_25_L_0_L_I_H_I_s2_x1 m hb0 hb2 hb5 hg0 hg2858 h4553

end R2N4
