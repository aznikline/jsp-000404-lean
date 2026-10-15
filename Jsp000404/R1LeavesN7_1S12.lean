import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S8
import Jsp000404.R1LeavesN7_1S10
import Jsp000404.R1LeavesN7_1S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6397 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h6398 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h6399 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 4 (by decide) (by decide) with h7162 | h7162
  · linarith only [h1, h7, h7162, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h7164 | h7164
    · linarith only [h1, h4553, h6, h6399, h7, h7164, hc12, hc34, hlam, hphi, ht23]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h7166 | h7166
      · linarith only [h2, h5072, h7166, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h7168 | h7168
        · linarith only [h5072, h6, h6397, h6399, h7168, hc34, hc45, hlam, hphi]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h7170 | h7170
          · linarith only [h4553, h6, h6398, h6399, h7168, h7170, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h7172 | h7172
            · linarith only [h5072, h6, h6398, h6399, h7172, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h7174 | h7174
              · linarith only [h5072, h6, h6398, h6399, h7168, h7174, hc23, hc34, hlam, hphi]
              · rcases h0bigk with h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c | h7176c
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [hlam, p7176_0]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h6, h6398, h6399, h7168, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7176_1]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  rcases p7176_3 (m.d 0 1) (by simp) with h7179 | h7179
                  · rcases p7176_3 (m.d 0 2) (by simp) with h7180 | h7180
                    · linarith only [h0, h7180, hlam]
                    · linarith only [h4, h7180, hlam]
                  · linarith only [h1, h7179, hlam]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  rcases p7176_3 (m.d 0 1) (by simp) with h7184 | h7184
                  · rcases p7176_3 (m.d 0 2) (by simp) with h7185 | h7185
                    · linarith only [h0, h7185, hlam]
                    · linarith only [h5, h7185, hlam]
                  · linarith only [h2, h7184, hlam]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h6, h6398, h6399, h7168, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7176_1]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h0, hlam, p7176_0]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [hlam, p7176_0]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  rcases p7176_3 (m.d 0 1) (by simp) with h7192 | h7192
                  · rcases p7176_3 (m.d 0 2) (by simp) with h7193 | h7193
                    · rcases p7176_3 (m.d 0 3) (by simp) with h7194 | h7194
                      · linarith only [h4, h7194, hlam]
                      · rcases p7176_3 (m.d 0 4) (by simp) with h7196 | h7196
                        · linarith only [h5, h7196, hlam]
                        · linarith only [h7, h7196, hlam]
                    · linarith only [h4, h7193, hlam]
                  · linarith only [h1, h7192, hlam]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  rcases p7176_3 (m.d 0 1) (by simp) with h7201 | h7201
                  · rcases p7176_3 (m.d 0 2) (by simp) with h7202 | h7202
                    · rcases p7176_3 (m.d 0 3) (by simp) with h7203 | h7203
                      · linarith only [h4, h7203, hlam]
                      · rcases p7176_3 (m.d 0 4) (by simp) with h7205 | h7205
                        · linarith only [h5, h7205, hlam]
                        · rcases p7176_3 (m.d 0 5) (by simp) with h7207 | h7207
                          · linarith only [h6, h7207, hlam]
                          · linarith only [h5072, h7207, hlam]
                    · linarith only [h5, h7202, hlam]
                  · linarith only [h2, h7201, hlam]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h6, h6398, h6399, h7168, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7176_1]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h1, hlam, p7176_1]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h4, hlam, p7176_1]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [hlam, p7176_0]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h7, hlam, p7176_1]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h4553, hlam, p7176_1]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h2, hlam, p7176_0]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h5, hlam, p7176_0]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h1, h6397, h7, h7174, hc23, hc45, hlam, hphi, ht34, p7176_1]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [hlam, p7176_0]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h5072, hlam, p7176_0]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h3, hlam, p7176_0]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [h6, hlam, p7176_1]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  rcases p7176_3 (m.d 0 1) (by simp) with h7225 | h7225
                  · rcases p7176_3 (m.d 0 2) (by simp) with h7226 | h7226
                    · rcases p7176_3 (m.d 0 3) (by simp) with h7227 | h7227
                      · linarith only [h4553, h7227, hlam]
                      · rcases p7176_3 (m.d 0 4) (by simp) with h7229 | h7229
                        · linarith only [h5072, h7229, hlam]
                        · linarith only [h7, h7229, hlam]
                    · linarith only [h4, h7226, hlam]
                  · linarith only [h1, h7225, hlam]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  rcases p7176_3 (m.d 0 1) (by simp) with h7234 | h7234
                  · rcases p7176_3 (m.d 0 2) (by simp) with h7235 | h7235
                    · rcases p7176_3 (m.d 0 3) (by simp) with h7236 | h7236
                      · linarith only [h4553, h7236, hlam]
                      · rcases p7176_3 (m.d 0 4) (by simp) with h7238 | h7238
                        · linarith only [h5072, h7238, hlam]
                        · rcases p7176_3 (m.d 0 5) (by simp) with h7240 | h7240
                          · rcases h2bigk with h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c | h7241c
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              rcases p7241_3 (m.d 0 2) (by simp) with h7243 | h7243
                              · rcases p7241_3 (m.d 1 2) (by simp) with h7244 | h7244
                                · linarith only [h0, h7244, hlam]
                                · rcases p7241_3 (m.d 2 3) (by simp) with h7246 | h7246
                                  · linarith only [h4, h7246, hlam]
                                  · rcases p7241_3 (m.d 2 4) (by simp) with h7248 | h7248
                                    · linarith only [h5, h7248, hlam]
                                    · rcases p7241_3 (m.d 2 5) (by simp) with h7250 | h7250
                                      · linarith only [h6, h7250, hlam]
                                      · linarith only [h6399, h7250, hlam]
                              · linarith only [h0, h7243, hlam]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h6, h6398, h6399, h7168, hlam, p7241_2]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h6, h6398, h6399, hlam, p7241_2]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h6398, h6399, h7168, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7241_1]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h0, hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h0, h6, h6399, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7241_1]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h4553, h6, h6399, h7168, hc23, hc35, hlam, hphi, p7241_1]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h6399, hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h4, hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h6397, hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h7168, hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h7170, hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h5, hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h6398, hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h5, h7, h7174, hc23, hc45, hlam, hphi, ht34, p7241_1]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h7172, hlam, p7241_1]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h6, hlam, p7241_0]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [h0, h6, h6397, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7241_1]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              rcases p7241_3 (m.d 0 2) (by simp) with h7274 | h7274
                              · rcases p7241_3 (m.d 1 2) (by simp) with h7275 | h7275
                                · linarith only [h6399, h7275, hlam]
                                · linarith only [h6397, h7275, hlam]
                              · linarith only [h4, h7274, hlam]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              rcases p7241_3 (m.d 0 2) (by simp) with h7279 | h7279
                              · rcases p7241_3 (m.d 1 2) (by simp) with h7280 | h7280
                                · linarith only [h6399, h7280, hlam]
                                · linarith only [h6398, h7280, hlam]
                              · linarith only [h5, h7279, hlam]
                            · have p7241_0 := h7241c.1
                              have p7241_1 := h7241c.2.1
                              have p7241_2 := h7241c.2.2.1
                              have p7241_3 := h7241c.2.2.2
                              linarith only [hlam, p7241_0]
                          · linarith only [h5072, h7240, hlam]
                    · linarith only [h5, h7235, hlam]
                  · linarith only [h2, h7234, hlam]
                · have p7176_0 := h7176c.1
                  have p7176_1 := h7176c.2.1
                  have p7176_2 := h7176c.2.2.1
                  have p7176_3 := h7176c.2.2.2
                  linarith only [hlam, p7176_0]

set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6397 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h6398 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 5 (by decide) (by decide) with h6399 | h6399
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072 h6397 h6398 h6399
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072 h6397 h6398 h6399

set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6397 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h6398 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  linarith only [h5, h5072, h6397, h6398, hc23, hc45, hlam, hphi, ht34]

set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6397 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 4 (by decide) (by decide) with h6398 | h6398
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072 h6397 h6398
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072 h6397 h6398

set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6397 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 4 (by decide) (by decide) with h7290 | h7290
  · linarith only [h4, h5072, h6397, h7, h7290, hc24, hc45, hlam, hphi]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h7292 | h7292
    · rcases m.htr 1 3 4 (by decide) (by decide) with h7293 | h7293
      · linarith only [h4, h6397, h7, h7292, h7293, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h7295 | h7295
        · linarith only [h4, h4553, h6397, h7295, hlam]
        · linarith only [h6397, h7292, h7295, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h7298 | h7298
      · linarith only [h1, h4, h6397, h7, h7298, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h7300 | h7300
        · linarith only [h4, h4553, h6397, h7300, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h7302 | h7302
          · linarith only [h5, h5072, h7290, h7302, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h7304 | h7304
            · linarith only [h4, h7, h7304, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h7306 | h7306
              · linarith only [h4, h4553, h7306, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7308 | h7308
                · linarith only [h5, h5072, h7308, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h7310 | h7310
                  · linarith only [h4, h5072, h6397, h7, h7310, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h4, h6397, h7, h7310, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 3 (by decide) (by decide) with h6397 | h6397
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072 h6397
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072 h6397

set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 4 5 (by decide) (by decide) with h5072 | h5072
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553 h5072

set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 3 5 (by decide) (by decide) with h4553 | h4553
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h4553

set_option maxHeartbeats 14612000 in
set_option maxHeartbeats 14612000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s6 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s7 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7

set_option maxHeartbeats 14892000 in
set_option maxHeartbeats 14892000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s5 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s6 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h7313 | h7313
    · rcases m.htr 0 3 5 (by decide) (by decide) with h7314 | h7314
      · linarith only [h4, h6, h7314, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7316 | h7316
        · linarith only [h5, h6, h7316, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7318 | h7318
          · rcases m.htr 1 2 4 (by decide) (by decide) with h7319 | h7319
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7320 | h7320
              · linarith only [h0, h6, h7320, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7322 | h7322
                · rcases m.htr 1 3 5 (by decide) (by decide) with h7323 | h7323
                  · linarith only [h1, h7314, h7323, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h7325 | h7325
                    · linarith only [h2, h7316, h7325, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h7327 | h7327
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h7328 | h7328
                        · linarith only [h0, h7314, h7318, h7328, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h7330 | h7330
                          · linarith only [h2, h4, h6, h7316, h7319, h7327, h7330, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h6, h7318, h7327, h7330, hc34, hc45, hlam, hphi]
                      · linarith only [h7313, h7314, h7327, hc23, hc35, hlam, hphi]
                · linarith only [h7313, h7314, h7322, hc13, hc35, hlam, hphi]
            · linarith only [h5, h6, h7319, hc12, hc25, hlam, hphi]
          · linarith only [h4, h6, h7318, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h7337 | h7337
      · linarith only [h5, h6, h7313, h7337, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7339 | h7339
        · linarith only [h5, h6, h7339, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7341 | h7341
          · rcases m.htr 1 2 4 (by decide) (by decide) with h7342 | h7342
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7343 | h7343
              · linarith only [h0, h6, h7343, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7345 | h7345
                · linarith only [h1, h7313, h7345, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h7347 | h7347
                  · linarith only [h1, h4, h6, h7337, h7347, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h7349 | h7349
                    · linarith only [h2, h7339, h7349, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h7351 | h7351
                      · linarith only [h4, h6, h7313, h7351, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h7353 | h7353
                        · linarith only [h4, h6, h7337, h7353, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h7355 | h7355
                          · linarith only [h3, h7313, h7339, h7342, h7343, h7355, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h7357 | h7357
                            · linarith only [h0, h6, h7342, h7351, h7355, h7357, hc23, hc34, hlam, hphi]
                            · rcases h0bigk with h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c | h7359c
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [hlam, p7359_0]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                rcases p7359_3 (m.d 0 1) (by simp) with h7361 | h7361
                                · rcases p7359_3 (m.d 0 2) (by simp) with h7362 | h7362
                                  · linarith only [h0, h7362, hlam]
                                  · rcases p7359_3 (m.d 0 3) (by simp) with h7364 | h7364
                                    · linarith only [h1, h7364, hlam]
                                    · rcases p7359_3 (m.d 0 4) (by simp) with h7366 | h7366
                                      · linarith only [h2, h7366, hlam]
                                      · rcases p7359_3 (m.d 0 5) (by simp) with h7368 | h7368
                                        · linarith only [h3, h7368, hlam]
                                        · linarith only [h6, h7368, hlam]
                                · linarith only [h0, h7361, hlam]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                rcases p7359_3 (m.d 0 1) (by simp) with h7372 | h7372
                                · rcases p7359_3 (m.d 0 2) (by simp) with h7373 | h7373
                                  · linarith only [h0, h7373, hlam]
                                  · linarith only [h4, h7373, hlam]
                                · linarith only [h1, h7372, hlam]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                rcases p7359_3 (m.d 0 1) (by simp) with h7377 | h7377
                                · rcases p7359_3 (m.d 0 2) (by simp) with h7378 | h7378
                                  · linarith only [h0, h7378, hlam]
                                  · linarith only [h5, h7378, hlam]
                                · linarith only [h2, h7377, hlam]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                rcases p7359_3 (m.d 0 1) (by simp) with h7382 | h7382
                                · rcases p7359_3 (m.d 0 2) (by simp) with h7383 | h7383
                                  · linarith only [h0, h7383, hlam]
                                  · rcases p7359_3 (m.d 0 3) (by simp) with h7385 | h7385
                                    · linarith only [h1, h7385, hlam]
                                    · rcases p7359_3 (m.d 0 4) (by simp) with h7387 | h7387
                                      · linarith only [h2, h7387, hlam]
                                      · rcases p7359_3 (m.d 0 5) (by simp) with h7389 | h7389
                                        · linarith only [h3, h7389, hlam]
                                        · rcases h2bigk with h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c | h7391c
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h6, h7342, h7351, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p7391_1]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h6, h7353, h7357, hc23, hc45, hlam, hphi, ht34, p7391_1]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h6, h7351, h7353, h7357, hc23, hc45, hlam, hphi, ht34, p7391_1]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h6, hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h0, hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7359_1, p7391_1]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h0, h6, h7351, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7359_1, p7391_1]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h7343, hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h4, hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h7341, hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h7351, hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h7353, hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h5, hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h7342, hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h5, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7359_1, p7391_1]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [hlam, p7391_0]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h7355, hlam, p7391_1]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h5, h7353, h7357, hc24, hc45, hlam, hphi, p7391_1]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [h7341, h7353, h7357, hc23, hc45, hlam, hphi, ht34, p7391_1]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            rcases p7391_3 (m.d 0 2) (by simp) with h7414 | h7414
                                            · linarith only [h6, h7414, hlam]
                                            · linarith only [h4, h7414, hlam]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            rcases p7391_3 (m.d 0 2) (by simp) with h7417 | h7417
                                            · linarith only [h6, h7417, hlam]
                                            · linarith only [h5, h7417, hlam]
                                          · have p7391_0 := h7391c.1
                                            have p7391_1 := h7391c.2.1
                                            have p7391_2 := h7391c.2.2.1
                                            have p7391_3 := h7391c.2.2.2
                                            linarith only [hlam, p7391_0]
                                · linarith only [h3, h7382, hlam]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h0, hlam, p7359_0]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [hlam, p7359_0]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h1, h6, h7341, h7353, h7357, hc23, hc45, hlam, hphi, ht34, p7359_1]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h2, h6, h7341, h7345, h7353, h7357, hc23, hc45, hlam, hphi, ht34, p7359_1]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h6, hlam, p7359_0]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h1, hlam, p7359_1]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h4, hlam, p7359_1]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [hlam, p7359_0]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h7313, hlam, p7359_1]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h7337, hlam, p7359_1]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h2, hlam, p7359_0]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h5, hlam, p7359_0]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h1, h5, h6, h7341, h7353, h7357, hc23, hc45, hlam, hphi, ht34, p7359_1]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [hlam, p7359_0]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h7339, hlam, p7359_0]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h3, hlam, p7359_0]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [h0, h6, h7342, h7351, h7353, h7357, hc23, hc45, hlam, hphi, ht34, p7359_1]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                rcases p7359_3 (m.d 0 1) (by simp) with h7439 | h7439
                                · rcases p7359_3 (m.d 0 2) (by simp) with h7440 | h7440
                                  · linarith only [h6, h7440, hlam]
                                  · linarith only [h4, h7440, hlam]
                                · linarith only [h1, h7439, hlam]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                rcases p7359_3 (m.d 0 1) (by simp) with h7444 | h7444
                                · rcases p7359_3 (m.d 0 2) (by simp) with h7445 | h7445
                                  · linarith only [h6, h7445, hlam]
                                  · linarith only [h5, h7445, hlam]
                                · linarith only [h2, h7444, hlam]
                              · have p7359_0 := h7359c.1
                                have p7359_1 := h7359c.2.1
                                have p7359_2 := h7359c.2.2.1
                                have p7359_3 := h7359c.2.2.2
                                linarith only [hlam, p7359_0]
            · linarith only [h5, h6, h7342, hc12, hc25, hlam, hphi]
          · linarith only [h4, h6, h7341, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 15632000 in
set_option maxHeartbeats 15632000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s4 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s5 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h7452 | h7452
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7453 | h7453
      · linarith only [h4, h5, h7453, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h7455 | h7455
        · rcases m.htr 0 4 5 (by decide) (by decide) with h7456 | h7456
          · rcases m.htr 1 2 3 (by decide) (by decide) with h7457 | h7457
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7458 | h7458
              · linarith only [h0, h5, h7452, h7458, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7460 | h7460
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7461 | h7461
                  · linarith only [h0, h5, h7453, h7455, h7457, h7461, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7463 | h7463
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7464 | h7464
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7465 | h7465
                        · linarith only [h4, h5, h7453, h7465, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7467 | h7467
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7468 | h7468
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7469 | h7469
                              · rcases h0bigk with h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c | h7470c
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [hlam, p7470_0]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h0, h7457, h7467, h7469, hc01, hc45, hlam, hphi, ht0b, ht5b, p7470_1]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  rcases p7470_3 (m.d 0 1) (by simp) with h7473 | h7473
                                  · rcases p7470_3 (m.d 0 2) (by simp) with h7474 | h7474
                                    · linarith only [h0, h7474, hlam]
                                    · linarith only [h4, h7474, hlam]
                                  · linarith only [h1, h7473, hlam]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h0, h5, h7457, h7467, h7469, hc01, hc45, hlam, hphi, ht0b, ht5b, p7470_1]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  rcases p7470_3 (m.d 0 1) (by simp) with h7479 | h7479
                                  · rcases p7470_3 (m.d 0 2) (by simp) with h7480 | h7480
                                    · linarith only [h0, h7480, hlam]
                                    · linarith only [h7452, h7480, hlam]
                                  · linarith only [h3, h7479, hlam]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h0, hlam, p7470_0]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [hlam, p7470_0]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h5, h7465, hc03, hc34, hlam, hphi, p7470_1]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h5, hlam, p7470_1]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  rcases p7470_3 (m.d 0 1) (by simp) with h7488 | h7488
                                  · rcases p7470_3 (m.d 0 2) (by simp) with h7489 | h7489
                                    · rcases p7470_3 (m.d 0 3) (by simp) with h7490 | h7490
                                      · linarith only [h4, h7490, hlam]
                                      · linarith only [h7455, h7490, hlam]
                                    · linarith only [h7452, h7489, hlam]
                                  · linarith only [h3, h7488, hlam]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h1, hlam, p7470_1]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h4, hlam, p7470_1]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [hlam, p7470_0]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h7453, hlam, p7470_1]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  rcases p7470_3 (m.d 0 1) (by simp) with h7499 | h7499
                                  · rcases p7470_3 (m.d 0 2) (by simp) with h7500 | h7500
                                    · rcases p7470_3 (m.d 0 3) (by simp) with h7501 | h7501
                                      · rcases p7470_3 (m.d 0 4) (by simp) with h7502 | h7502
                                        · rcases p7470_3 (m.d 0 5) (by simp) with h7503 | h7503
                                          · linarith only [h7455, h7503, hlam]
                                          · rcases h2bigk with h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c | h7505c
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h5, h7465, hc12, hc34, hlam, hphi, ht23, p7505_1]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h5, h7465, hc23, hc34, hlam, hphi, p7505_1]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h5, hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              rcases p7505_3 (m.d 0 2) (by simp) with h7510 | h7510
                                              · rcases p7505_3 (m.d 1 2) (by simp) with h7511 | h7511
                                                · linarith only [h0, h7511, hlam]
                                                · linarith only [h7460, h7511, hlam]
                                              · linarith only [h7510, hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h0, hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h0, h7467, h7469, hc01, hc45, hlam, hphi, ht0b, ht5b, p7505_1]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h7458, hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              rcases p7505_3 (m.d 0 2) (by simp) with h7519 | h7519
                                              · rcases p7505_3 (m.d 1 2) (by simp) with h7520 | h7520
                                                · rcases p7505_3 (m.d 2 3) (by simp) with h7521 | h7521
                                                  · linarith only [h7457, h7521, hlam]
                                                  · linarith only [h7467, h7521, hlam]
                                                · linarith only [h7520, hlam, p7505_0]
                                              · linarith only [h7452, h7519, hlam]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h4, hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h7457, hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h7465, hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h4, h5, h7465, h7467, h7469, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7505_1]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h4, h7465, hc23, hc34, hlam, hphi, p7505_1]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h7457, h7465, hc23, hc34, hlam, hphi, p7505_1]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              rcases p7505_3 (m.d 0 2) (by simp) with h7533 | h7533
                                              · linarith only [h5, h7533, hlam]
                                              · linarith only [h4, h7533, hlam]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h3, h4, h5, h7460, hlam, p7470_1, p7505_2]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h7452, hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h7460, hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h7467, hlam, p7505_1]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [h7468, hlam, p7505_0]
                                            · have p7505_0 := h7505c.1
                                              have p7505_1 := h7505c.2.1
                                              have p7505_2 := h7505c.2.2.1
                                              have p7505_3 := h7505c.2.2.2
                                              linarith only [hlam, p7505_0]
                                        · linarith only [h7456, h7502, hlam]
                                      · linarith only [h7455, h7501, hlam]
                                    · linarith only [h7452, h7500, hlam]
                                  · linarith only [h3, h7499, hlam]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h2, hlam, p7470_0]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h0, h7457, h7467, h7469, hc04, hc45, hlam, hphi, ht0b, ht5b, p7470_1]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  rcases p7470_3 (m.d 0 1) (by simp) with h7549 | h7549
                                  · rcases p7470_3 (m.d 0 2) (by simp) with h7550 | h7550
                                    · linarith only [h5, h7550, hlam]
                                    · linarith only [h4, h7550, hlam]
                                  · linarith only [h1, h7549, hlam]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [hlam, p7470_0]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  rcases p7470_3 (m.d 0 1) (by simp) with h7555 | h7555
                                  · rcases p7470_3 (m.d 0 2) (by simp) with h7556 | h7556
                                    · linarith only [h5, h7556, hlam]
                                    · linarith only [h7452, h7556, hlam]
                                  · linarith only [h3, h7555, hlam]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h3, hlam, p7470_0]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h7452, hlam, p7470_1]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h7455, hlam, p7470_0]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [h7456, hlam, p7470_1]
                                · have p7470_0 := h7470c.1
                                  have p7470_1 := h7470c.2.1
                                  have p7470_2 := h7470c.2.2.1
                                  have p7470_3 := h7470c.2.2.2
                                  linarith only [hlam, p7470_0]
                              · linarith only [h7453, h7456, h7469, hlam]
                            · linarith only [h0, h5, h7457, h7463, h7464, h7467, h7468, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h4, h5, h7455, h7465, h7467, hc23, hc34, hlam, hphi]
                      · linarith only [h7453, h7455, h7456, h7457, h7458, h7464, hc23, hc34, hlam, hphi]
                    · linarith only [h7453, h7455, h7463, hc13, hc34, hlam, hphi]
                · linarith only [h5, h7452, h7457, h7460, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h4, h5, h7457, hc12, hc24, hlam, hphi]
          · linarith only [h5, h7452, h7456, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h7573 | h7573
          · rcases m.htr 1 2 3 (by decide) (by decide) with h7574 | h7574
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7575 | h7575
              · linarith only [h0, h5, h7575, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7577 | h7577
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7578 | h7578
                  · linarith only [h1, h7453, h7578, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7580 | h7580
                    · linarith only [h1, h7455, h7580, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7582 | h7582
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7583 | h7583
                        · linarith only [h1, h4, h5, h7453, h7583, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7585 | h7585
                          · linarith only [h3, h7455, h7574, h7580, h7585, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7587 | h7587
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7588 | h7588
                              · rcases h0bigk with h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c | h7589c
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [hlam, p7589_0]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  rcases p7589_3 (m.d 0 1) (by simp) with h7591 | h7591
                                  · rcases p7589_3 (m.d 0 2) (by simp) with h7592 | h7592
                                    · linarith only [h0, h7592, hlam]
                                    · rcases p7589_3 (m.d 0 3) (by simp) with h7594 | h7594
                                      · linarith only [h1, h7594, hlam]
                                      · rcases p7589_3 (m.d 0 4) (by simp) with h7596 | h7596
                                        · linarith only [h2, h7596, hlam]
                                        · linarith only [h5, h7596, hlam]
                                  · linarith only [h0, h7591, hlam]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  rcases p7589_3 (m.d 0 1) (by simp) with h7600 | h7600
                                  · rcases p7589_3 (m.d 0 2) (by simp) with h7601 | h7601
                                    · linarith only [h0, h7601, hlam]
                                    · linarith only [h4, h7601, hlam]
                                  · linarith only [h1, h7600, hlam]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  rcases p7589_3 (m.d 0 1) (by simp) with h7605 | h7605
                                  · rcases p7589_3 (m.d 0 2) (by simp) with h7606 | h7606
                                    · linarith only [h0, h7606, hlam]
                                    · rcases p7589_3 (m.d 0 3) (by simp) with h7608 | h7608
                                      · linarith only [h1, h7608, hlam]
                                      · rcases p7589_3 (m.d 0 4) (by simp) with h7610 | h7610
                                        · linarith only [h2, h7610, hlam]
                                        · rcases p7589_3 (m.d 0 5) (by simp) with h7612 | h7612
                                          · linarith only [h3, h7612, hlam]
                                          · rcases h2bigk with h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c | h7614c
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h5, h7577, h7585, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7589_1, p7614_1]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7589_1, p7614_1]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h5, hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h5, h7585, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7589_1, p7614_1]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h0, hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7589_1, p7614_1]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h7575, hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h0, h5, h7585, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7589_1, p7614_1]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h4, hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h7574, hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h7583, hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h7585, hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h4, h7583, hc23, hc34, hlam, hphi, p7614_1]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h7574, h7583, hc23, hc34, hlam, hphi, p7614_1]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              rcases p7614_3 (m.d 0 2) (by simp) with h7632 | h7632
                                              · linarith only [h5, h7632, hlam]
                                              · linarith only [h4, h7632, hlam]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              rcases p7614_3 (m.d 0 2) (by simp) with h7636 | h7636
                                              · linarith only [h5, h7636, hlam]
                                              · linarith only [h7452, h7636, hlam]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h7452, hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h7577, hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h0, h7577, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7614_1]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [h7587, hlam, p7614_0]
                                            · have p7614_0 := h7614c.1
                                              have p7614_1 := h7614c.2.1
                                              have p7614_2 := h7614c.2.2.1
                                              have p7614_3 := h7614c.2.2.2
                                              linarith only [hlam, p7614_0]
                                  · linarith only [h2, h7605, hlam]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  rcases p7589_3 (m.d 0 1) (by simp) with h7645 | h7645
                                  · rcases p7589_3 (m.d 0 2) (by simp) with h7646 | h7646
                                    · linarith only [h0, h7646, hlam]
                                    · linarith only [h7452, h7646, hlam]
                                  · linarith only [h3, h7645, hlam]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h0, hlam, p7589_0]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [hlam, p7589_0]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h5, h7583, hc03, hc34, hlam, hphi, p7589_1]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h5, hlam, p7589_1]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h3, h5, h7580, h7583, hc13, hc34, hlam, hphi, p7589_1]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h1, hlam, p7589_1]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h4, hlam, p7589_1]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [hlam, p7589_0]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h7453, hlam, p7589_1]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h7455, hlam, p7589_1]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h2, hlam, p7589_0]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h4, h5, h7583, hc23, hc34, hlam, hphi, p7589_1]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  rcases p7589_3 (m.d 0 1) (by simp) with h7662 | h7662
                                  · rcases p7589_3 (m.d 0 2) (by simp) with h7663 | h7663
                                    · linarith only [h5, h7663, hlam]
                                    · linarith only [h4, h7663, hlam]
                                  · linarith only [h1, h7662, hlam]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [hlam, p7589_0]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  rcases p7589_3 (m.d 0 1) (by simp) with h7668 | h7668
                                  · rcases p7589_3 (m.d 0 2) (by simp) with h7669 | h7669
                                    · linarith only [h5, h7669, hlam]
                                    · linarith only [h7452, h7669, hlam]
                                  · linarith only [h3, h7668, hlam]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h3, hlam, p7589_0]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h7452, hlam, p7589_1]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h1, h5, h7452, h7574, h7583, hc23, hc34, hlam, hphi, p7589_1]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [h7573, hlam, p7589_1]
                                · have p7589_0 := h7589c.1
                                  have p7589_1 := h7589c.2.1
                                  have p7589_2 := h7589c.2.2.1
                                  have p7589_3 := h7589c.2.2.2
                                  linarith only [hlam, p7589_0]
                              · linarith only [h0, h5, h7577, h7583, h7585, h7588, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h0, h5, h7577, h7585, h7587, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h7453, h7573, h7574, h7575, h7582, hc23, hc34, hlam, hphi]
                · linarith only [h5, h7452, h7574, h7577, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h4, h5, h7574, hc12, hc24, hlam, hphi]
          · linarith only [h5, h7452, h7573, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h7684 | h7684
      · linarith only [h4, h5, h7684, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h7686 | h7686
        · linarith only [h4, h7452, h7686, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h7688 | h7688
          · rcases m.htr 1 2 3 (by decide) (by decide) with h7689 | h7689
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7690 | h7690
              · linarith only [h0, h5, h7690, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7692 | h7692
                · linarith only [h0, h7452, h7692, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7694 | h7694
                  · linarith only [h1, h7684, h7694, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7696 | h7696
                    · linarith only [h1, h7686, h7696, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7698 | h7698
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7699 | h7699
                        · linarith only [h0, h1, h5, h7684, h7689, h7699, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7701 | h7701
                          · linarith only [h4, h7452, h7686, h7701, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7703 | h7703
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7704 | h7704
                              · rcases h0bigk with h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c | h7705c
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [hlam, p7705_0]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  rcases p7705_3 (m.d 0 1) (by simp) with h7707 | h7707
                                  · rcases p7705_3 (m.d 0 2) (by simp) with h7708 | h7708
                                    · linarith only [h0, h7708, hlam]
                                    · rcases p7705_3 (m.d 0 3) (by simp) with h7710 | h7710
                                      · linarith only [h1, h7710, hlam]
                                      · rcases p7705_3 (m.d 0 4) (by simp) with h7712 | h7712
                                        · linarith only [h2, h7712, hlam]
                                        · linarith only [h5, h7712, hlam]
                                  · linarith only [h0, h7707, hlam]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  rcases p7705_3 (m.d 0 1) (by simp) with h7716 | h7716
                                  · rcases p7705_3 (m.d 0 2) (by simp) with h7717 | h7717
                                    · linarith only [h0, h7717, hlam]
                                    · linarith only [h4, h7717, hlam]
                                  · linarith only [h1, h7716, hlam]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  rcases p7705_3 (m.d 0 1) (by simp) with h7721 | h7721
                                  · rcases p7705_3 (m.d 0 2) (by simp) with h7722 | h7722
                                    · linarith only [h0, h7722, hlam]
                                    · rcases p7705_3 (m.d 0 3) (by simp) with h7724 | h7724
                                      · linarith only [h1, h7724, hlam]
                                      · rcases p7705_3 (m.d 0 4) (by simp) with h7726 | h7726
                                        · linarith only [h2, h7726, hlam]
                                        · rcases p7705_3 (m.d 0 5) (by simp) with h7728 | h7728
                                          · linarith only [h3, h7728, hlam]
                                          · rcases h2bigk with h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c | h7730c
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h7452, h7703, hc12, hc24, hlam, hphi, p7730_1]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h7452, h7688, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7705_1, p7730_1]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h5, hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h7452, hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h0, hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h0, h7452, h7688, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7705_1, p7730_1]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h7690, hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h7692, hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h4, hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h7689, hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h7699, hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h7701, hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h4, h7699, hc23, hc34, hlam, hphi, p7730_1]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h7689, h7699, hc23, hc34, hlam, hphi, p7730_1]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              rcases p7730_3 (m.d 0 2) (by simp) with h7748 | h7748
                                              · linarith only [h5, h7748, hlam]
                                              · linarith only [h4, h7748, hlam]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h0, h7452, h7689, h7699, hc23, hc34, hlam, hphi, p7730_1]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h0, h7689, h7701, hc23, hc35, hlam, hphi, p7730_1]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h7689, h7701, hc23, hc35, hlam, hphi, p7730_1]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              rcases p7730_3 (m.d 0 2) (by simp) with h7755 | h7755
                                              · linarith only [h7452, h7755, hlam]
                                              · linarith only [h4, h7755, hlam]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [h7703, hlam, p7730_0]
                                            · have p7730_0 := h7730c.1
                                              have p7730_1 := h7730c.2.1
                                              have p7730_2 := h7730c.2.2.1
                                              have p7730_3 := h7730c.2.2.2
                                              linarith only [hlam, p7730_0]
                                  · linarith only [h2, h7721, hlam]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  rcases p7705_3 (m.d 0 1) (by simp) with h7761 | h7761
                                  · rcases p7705_3 (m.d 0 2) (by simp) with h7762 | h7762
                                    · linarith only [h0, h7762, hlam]
                                    · rcases p7705_3 (m.d 0 3) (by simp) with h7764 | h7764
                                      · linarith only [h1, h7764, hlam]
                                      · rcases p7705_3 (m.d 0 4) (by simp) with h7766 | h7766
                                        · linarith only [h2, h7766, hlam]
                                        · linarith only [h7688, h7766, hlam]
                                  · linarith only [h3, h7761, hlam]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h0, hlam, p7705_0]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [hlam, p7705_0]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h1, h5, h7699, hc13, hc34, hlam, hphi, p7705_1]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h5, hlam, p7705_1]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h7452, hlam, p7705_0]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h1, hlam, p7705_1]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h4, hlam, p7705_1]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [hlam, p7705_0]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h7684, hlam, p7705_1]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h7686, hlam, p7705_1]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h2, hlam, p7705_0]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h4, h7684, hc23, hc34, hlam, hphi, p7705_1]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  rcases p7705_3 (m.d 0 1) (by simp) with h7782 | h7782
                                  · rcases p7705_3 (m.d 0 2) (by simp) with h7783 | h7783
                                    · linarith only [h5, h7783, hlam]
                                    · linarith only [h4, h7783, hlam]
                                  · linarith only [h1, h7782, hlam]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [hlam, p7705_0]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h0, h5, h7452, h7689, h7699, hc23, hc34, hlam, hphi, p7705_1]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h3, hlam, p7705_0]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h0, h7452, h7689, h7699, h7703, hc23, hc34, hlam, hphi, p7705_1]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  rcases p7705_3 (m.d 0 1) (by simp) with h7791 | h7791
                                  · rcases p7705_3 (m.d 0 2) (by simp) with h7792 | h7792
                                    · linarith only [h7452, h7792, hlam]
                                    · linarith only [h4, h7792, hlam]
                                  · linarith only [h1, h7791, hlam]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [h7688, hlam, p7705_1]
                                · have p7705_0 := h7705c.1
                                  have p7705_1 := h7705c.2.1
                                  have p7705_2 := h7705c.2.2.1
                                  have p7705_3 := h7705c.2.2.2
                                  linarith only [hlam, p7705_0]
                              · linarith only [h2, h5, h7698, h7699, h7704, hlam]
                            · linarith only [h2, h5, h7698, h7703, hlam]
                      · linarith only [h7684, h7688, h7689, h7690, h7698, hc23, hc34, hlam, hphi]
            · linarith only [h4, h7452, h7689, hc12, hc25, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h7802 | h7802
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7803 | h7803
              · linarith only [h0, h5, h7803, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7805 | h7805
                · linarith only [h0, h7452, h7805, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7807 | h7807
                  · linarith only [h1, h7684, h7807, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7809 | h7809
                    · linarith only [h1, h7686, h7809, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7811 | h7811
                      · linarith only [h0, h2, h5, h7688, h7802, h7811, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7813 | h7813
                        · linarith only [h0, h1, h5, h7684, h7802, h7813, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7815 | h7815
                          · linarith only [h4, h5, h7686, h7688, h7815, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7817 | h7817
                            · linarith only [h0, h5, h7688, h7802, h7813, h7817, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h5, h7802, h7817, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h4, h5, h7802, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  linarith only [h0, h4, h9968, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9970 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  linarith only [h0, h7821, h9970, hlam]

end R2N4
