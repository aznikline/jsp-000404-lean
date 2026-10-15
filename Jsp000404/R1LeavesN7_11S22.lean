import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S21

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11650 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11651 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11652 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11653 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 1 2 3 (by decide) (by decide) with h13154 | h13154
  · rcases m.htr 1 2 5 (by decide) (by decide) with h13155 | h13155
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13156 | h13156
      · rcases m.htr 1 3 5 (by decide) (by decide) with h13157 | h13157
        · rcases m.htr 1 4 5 (by decide) (by decide) with h13158 | h13158
          · linarith only [h11653, h13158, hc14, hlam, hphi, ht01, u0ehi3]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13160 | h13160
            · rcases m.htr 2 3 5 (by decide) (by decide) with h13161 | h13161
              · rcases m.htr 2 4 5 (by decide) (by decide) with h13162 | h13162
                · linarith only [h10008, h11648, h13158, h13160, h13162, hc02, hlam, hphi, u0ehi0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h13164 | h13164
                  · linarith only [h0, h10008, h11648, h13158, h13160, h13164, hc12, hlam, hphi, ht01, u0ehi0]
                  · rcases h2bigk with h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c | h13166c
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [h0, hlam, p13166_1]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      rcases p13166_3 (m.d 0 2) (by simp) with h13169 | h13169
                      · rcases p13166_3 (m.d 1 2) (by simp) with h13170 | h13170
                        · rcases p13166_3 (m.d 2 3) (by simp) with h13171 | h13171
                          · linarith only [h13171, hlam, p13166_0]
                          · rcases p13166_3 (m.d 2 4) (by simp) with h13173 | h13173
                            · linarith only [h11649, h13173, hlam]
                            · rcases p13166_3 (m.d 2 5) (by simp) with h13175 | h13175
                              · linarith only [h11650, h13175, hlam]
                              · rcases h3bigk with h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c | h13177c
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h8410, hlam, p13177_1]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  rcases p13177_3 (m.d 0 3) (by simp) with h13180 | h13180
                                  · rcases p13177_3 (m.d 1 3) (by simp) with h13181 | h13181
                                    · rcases p13177_3 (m.d 2 3) (by simp) with h13182 | h13182
                                      · linarith only [h11648, h13182, hlam]
                                      · rcases p13177_3 (m.d 3 4) (by simp) with h13184 | h13184
                                        · linarith only [h11651, h13184, hlam]
                                        · rcases p13177_3 (m.d 3 5) (by simp) with h13186 | h13186
                                          · linarith only [h11652, h13186, hlam]
                                          · rcases h5bigk with h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c | h13188c
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [hlam, p13188_0]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h10008, hlam, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h10008, h13158, h13162, hc24, hc45, hlam, hphi, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h10008, h13158, h13164, hc34, hc45, hlam, hphi, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h11653, hlam, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h0, h11648, h13158, h13161, h13164, hc12, hc34, hc45, hlam, hphi, ht01, p13177_1, p13188_1, u0ehi4]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [hlam, p13188_0]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h13158, h13162, hc24, hc45, hlam, hphi, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h13158, h13164, hc34, hc45, hlam, hphi, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h13158, hlam, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h11650, hlam, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h13155, hlam, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [hlam, p13188_0]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h0, h11650, h13164, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h13162, hlam, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h11652, hlam, p13188_0]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h13157, hlam, p13188_0]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h13161, hlam, p13188_0]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [hlam, p13188_0]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h13164, hlam, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h10008, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p13188_1, u0ehi0]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h10008, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p13188_1, u0ehi0]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h13161, h13164, hc34, hc45, hlam, hphi, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [h13164, hc34, hc45, hlam, hphi, p13188_1]
                                            · have p13188_0 := h13188c.1
                                              have p13188_1 := h13188c.2.1
                                              have p13188_2 := h13188c.2.2.1
                                              have p13188_3 := h13188c.2.2.2
                                              linarith only [hlam, p13188_0]
                                    · linarith only [h13154, h13181, hlam]
                                  · linarith only [h11648, h13180, hlam]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  rcases p13177_3 (m.d 0 3) (by simp) with h13216 | h13216
                                  · rcases p13177_3 (m.d 1 3) (by simp) with h13217 | h13217
                                    · rcases p13177_3 (m.d 2 3) (by simp) with h13218 | h13218
                                      · linarith only [h11648, h13218, hlam]
                                      · linarith only [h13160, h13218, hlam]
                                    · linarith only [h13156, h13217, hlam]
                                  · linarith only [h13216, hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  rcases p13177_3 (m.d 0 3) (by simp) with h13223 | h13223
                                  · rcases p13177_3 (m.d 1 3) (by simp) with h13224 | h13224
                                    · rcases p13177_3 (m.d 2 3) (by simp) with h13225 | h13225
                                      · linarith only [h11648, h13225, hlam]
                                      · linarith only [h13161, h13225, hlam]
                                    · linarith only [h13157, h13224, hlam]
                                  · linarith only [h13223, hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [hc13, hlam, hphi, ht01, p13177_1, u0ehi2]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  rcases p13177_3 (m.d 0 3) (by simp) with h13232 | h13232
                                  · linarith only [h13232, h8410, hlam]
                                  · linarith only [h11648, h13232, hlam]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  rcases p13177_3 (m.d 0 3) (by simp) with h13235 | h13235
                                  · linarith only [h13235, h8410, hlam]
                                  · linarith only [h11651, h13235, hlam]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  rcases p13177_3 (m.d 0 3) (by simp) with h13238 | h13238
                                  · linarith only [h13238, h8410, hlam]
                                  · linarith only [h11652, h13238, hlam]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h11648, hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h13154, hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13166_1, p13177_1]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p13166_1, p13177_1]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h11651, hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h13156, hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h13160, hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h13164, hlam, p13177_1]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h11652, hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h13157, hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h13161, hlam, p13177_0]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [h0, h13161, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13166_1, p13177_1]
                                · have p13177_0 := h13177c.1
                                  have p13177_1 := h13177c.2.1
                                  have p13177_2 := h13177c.2.2.1
                                  have p13177_3 := h13177c.2.2.2
                                  linarith only [hlam, p13177_0]
                        · linarith only [h13154, h13170, hlam]
                      · linarith only [h13169, hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      rcases p13166_3 (m.d 0 2) (by simp) with h13258 | h13258
                      · rcases p13166_3 (m.d 1 2) (by simp) with h13259 | h13259
                        · rcases p13166_3 (m.d 2 3) (by simp) with h13260 | h13260
                          · linarith only [h11648, h13260, hlam]
                          · linarith only [h13160, h13260, hlam]
                        · linarith only [h0, h13259, hlam, p13166_1]
                      · linarith only [h13258, hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      rcases p13166_3 (m.d 0 2) (by simp) with h13265 | h13265
                      · rcases p13166_3 (m.d 1 2) (by simp) with h13266 | h13266
                        · rcases p13166_3 (m.d 2 3) (by simp) with h13267 | h13267
                          · linarith only [h11648, h13267, hlam]
                          · linarith only [h13161, h13267, hlam]
                        · linarith only [h13155, h13266, hlam]
                      · linarith only [h13265, hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [hc12, hlam, hphi, ht01, p13166_1, u0ehi1]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      rcases p13166_3 (m.d 0 2) (by simp) with h13274 | h13274
                      · linarith only [h0, h13274, hlam]
                      · linarith only [h11648, h13274, hlam]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      rcases p13166_3 (m.d 0 2) (by simp) with h13277 | h13277
                      · linarith only [h0, h13277, hlam]
                      · linarith only [h11649, h13277, hlam]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      rcases p13166_3 (m.d 0 2) (by simp) with h13280 | h13280
                      · linarith only [h0, h13280, hlam]
                      · linarith only [h11650, h13280, hlam]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [h11648, hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [h13154, hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      rcases p13166_3 (m.d 0 2) (by simp) with h13286 | h13286
                      · rcases p13166_3 (m.d 1 2) (by simp) with h13287 | h13287
                        · rcases p13166_3 (m.d 2 3) (by simp) with h13288 | h13288
                          · rcases p13166_3 (m.d 2 4) (by simp) with h13289 | h13289
                            · linarith only [h13160, h13289, hlam]
                            · rcases p13166_3 (m.d 2 5) (by simp) with h13291 | h13291
                              · linarith only [h13161, h13291, hlam]
                              · linarith only [h13162, h13291, hlam]
                          · linarith only [h13160, h13288, hlam]
                        · linarith only [h0, h11648, h13287, hlam, p13166_1]
                      · linarith only [h11649, h13286, hlam]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      rcases p13166_3 (m.d 0 2) (by simp) with h13297 | h13297
                      · rcases p13166_3 (m.d 1 2) (by simp) with h13298 | h13298
                        · rcases p13166_3 (m.d 2 3) (by simp) with h13299 | h13299
                          · rcases p13166_3 (m.d 2 4) (by simp) with h13300 | h13300
                            · linarith only [h13160, h13300, hlam]
                            · rcases p13166_3 (m.d 2 5) (by simp) with h13302 | h13302
                              · linarith only [h13161, h13302, hlam]
                              · rcases h3bigk with h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h8410, hlam, p13304_1]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h13160, h13162, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p13166_1, p13304_1]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  rcases p13304_3 (m.d 0 3) (by simp) with h13308 | h13308
                                  · rcases p13304_3 (m.d 1 3) (by simp) with h13309 | h13309
                                    · rcases p13304_3 (m.d 2 3) (by simp) with h13310 | h13310
                                      · linarith only [h11648, h13310, hlam]
                                      · linarith only [h13160, h13310, hlam]
                                    · linarith only [h13156, h13309, hlam]
                                  · linarith only [h13308, hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  rcases p13304_3 (m.d 0 3) (by simp) with h13315 | h13315
                                  · rcases p13304_3 (m.d 1 3) (by simp) with h13316 | h13316
                                    · rcases p13304_3 (m.d 2 3) (by simp) with h13317 | h13317
                                      · linarith only [h11648, h13317, hlam]
                                      · linarith only [h13161, h13317, hlam]
                                    · linarith only [h13157, h13316, hlam]
                                  · linarith only [h13315, hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h13154, hc12, hlam, hphi, ht01, p13304_1, u0ehi2]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h13154, h13160, h13162, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13166_1, p13304_1]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  rcases p13304_3 (m.d 0 3) (by simp) with h13325 | h13325
                                  · linarith only [h13325, h8410, hlam]
                                  · linarith only [h11651, h13325, hlam]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  rcases p13304_3 (m.d 0 3) (by simp) with h13328 | h13328
                                  · linarith only [h13328, h8410, hlam]
                                  · linarith only [h11652, h13328, hlam]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h11648, hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h13154, hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  rcases p13304_3 (m.d 0 3) (by simp) with h13334 | h13334
                                  · rcases p13304_3 (m.d 1 3) (by simp) with h13335 | h13335
                                    · rcases p13304_3 (m.d 2 3) (by simp) with h13336 | h13336
                                      · rcases p13304_3 (m.d 3 4) (by simp) with h13337 | h13337
                                        · linarith only [h13337, hlam, p13304_0]
                                        · rcases p13304_3 (m.d 3 5) (by simp) with h13339 | h13339
                                          · linarith only [h13161, h13339, hlam]
                                          · linarith only [h13164, h13339, hlam]
                                      · linarith only [h13336, hlam, p13304_0]
                                    · linarith only [h13156, h13335, hlam]
                                  · linarith only [h11651, h13334, hlam]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  rcases p13304_3 (m.d 0 3) (by simp) with h13345 | h13345
                                  · rcases p13304_3 (m.d 1 3) (by simp) with h13346 | h13346
                                    · rcases p13304_3 (m.d 2 3) (by simp) with h13347 | h13347
                                      · rcases p13304_3 (m.d 3 4) (by simp) with h13348 | h13348
                                        · linarith only [h13160, h13348, hlam]
                                        · rcases p13304_3 (m.d 3 5) (by simp) with h13350 | h13350
                                          · linarith only [h13350, hlam, p13304_0]
                                          · rcases h5bigk with h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c | h13352c
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [hlam, p13352_0]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h10008, hlam, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h11653, h13160, h13162, hc34, hc45, hlam, hphi, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h10008, h13158, h13164, hc34, hc45, hlam, hphi, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h11653, hlam, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h13158, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p13352_1, u0ehi4]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [hlam, p13352_0]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h13158, h13160, h13162, hc34, hc45, hlam, hphi, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h13158, h13164, hc34, hc45, hlam, hphi, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h13158, hlam, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h11650, hlam, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h13155, hlam, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [hlam, p13352_0]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h0, h11648, h13164, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13166_1, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h13162, hlam, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h11652, hlam, p13352_0]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h13157, hlam, p13352_0]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h13161, hlam, p13352_0]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [hlam, p13352_0]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h13164, hlam, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h10008, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p13352_1, u0ehi0]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h10008, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p13352_1, u0ehi0]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h13160, h13162, hc34, hc45, hlam, hphi, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [h13164, hc34, hc45, hlam, hphi, p13352_1]
                                            · have p13352_0 := h13352c.1
                                              have p13352_1 := h13352c.2.1
                                              have p13352_2 := h13352c.2.2.1
                                              have p13352_3 := h13352c.2.2.2
                                              linarith only [hlam, p13352_0]
                                      · linarith only [h13347, hlam, p13304_0]
                                    · linarith only [h13157, h13346, hlam]
                                  · linarith only [h11652, h13345, hlam]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h11651, hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h13156, hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h13160, hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h13164, hlam, p13304_1]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h11652, hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h13157, hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h13161, hlam, p13304_0]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [h0, h11648, h13161, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13304_1]
                                · have p13304_0 := h13304c.1
                                  have p13304_1 := h13304c.2.1
                                  have p13304_2 := h13304c.2.2.1
                                  have p13304_3 := h13304c.2.2.2
                                  linarith only [hlam, p13304_0]
                          · linarith only [h13161, h13299, hlam]
                        · linarith only [h13155, h13298, hlam]
                      · linarith only [h11650, h13297, hlam]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [h11649, hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [h0, h13162, hc25, hlam, hphi, ht01, ht12, p13166_1, u0ehi1]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [h13160, hlam, p13166_1]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [h13162, hlam, p13166_1]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [h11650, hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [h13155, hlam, p13166_0]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [h13161, hlam, p13166_1]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      rcases p13166_3 (m.d 0 2) (by simp) with h13402 | h13402
                      · rcases p13166_3 (m.d 1 2) (by simp) with h13403 | h13403
                        · rcases p13166_3 (m.d 2 3) (by simp) with h13404 | h13404
                          · rcases p13166_3 (m.d 2 4) (by simp) with h13405 | h13405
                            · linarith only [h13162, h13405, hlam]
                            · rcases p13166_3 (m.d 2 5) (by simp) with h13407 | h13407
                              · rcases h3bigk with h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c | h13408c
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h8410, hlam, p13408_1]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h13161, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p13166_1, p13408_1]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  rcases p13408_3 (m.d 0 3) (by simp) with h13412 | h13412
                                  · rcases p13408_3 (m.d 1 3) (by simp) with h13413 | h13413
                                    · rcases p13408_3 (m.d 2 3) (by simp) with h13414 | h13414
                                      · linarith only [h11648, h13414, hlam]
                                      · linarith only [h13160, h13414, hlam]
                                    · linarith only [h13156, h13413, hlam]
                                  · linarith only [h13412, hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  rcases p13408_3 (m.d 0 3) (by simp) with h13419 | h13419
                                  · rcases p13408_3 (m.d 1 3) (by simp) with h13420 | h13420
                                    · rcases p13408_3 (m.d 2 3) (by simp) with h13421 | h13421
                                      · linarith only [h11648, h13421, hlam]
                                      · linarith only [h13161, h13421, hlam]
                                    · linarith only [h13157, h13420, hlam]
                                  · linarith only [h13419, hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h13154, hc12, hlam, hphi, ht01, p13408_1, u0ehi2]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h13154, h13160, h13161, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13166_1, p13408_1]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  rcases p13408_3 (m.d 0 3) (by simp) with h13429 | h13429
                                  · linarith only [h13429, h8410, hlam]
                                  · linarith only [h11651, h13429, hlam]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  rcases p13408_3 (m.d 0 3) (by simp) with h13432 | h13432
                                  · linarith only [h13432, h8410, hlam]
                                  · linarith only [h11652, h13432, hlam]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h11648, hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h13154, hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  rcases p13408_3 (m.d 0 3) (by simp) with h13438 | h13438
                                  · rcases p13408_3 (m.d 1 3) (by simp) with h13439 | h13439
                                    · rcases p13408_3 (m.d 2 3) (by simp) with h13440 | h13440
                                      · rcases p13408_3 (m.d 3 4) (by simp) with h13441 | h13441
                                        · linarith only [h13441, hlam, p13408_0]
                                        · rcases p13408_3 (m.d 3 5) (by simp) with h13443 | h13443
                                          · linarith only [h13161, h13443, hlam]
                                          · linarith only [h13164, h13443, hlam]
                                      · linarith only [h13440, hlam, p13408_0]
                                    · linarith only [h13156, h13439, hlam]
                                  · linarith only [h11651, h13438, hlam]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  rcases p13408_3 (m.d 0 3) (by simp) with h13449 | h13449
                                  · rcases p13408_3 (m.d 1 3) (by simp) with h13450 | h13450
                                    · rcases p13408_3 (m.d 2 3) (by simp) with h13451 | h13451
                                      · rcases p13408_3 (m.d 3 4) (by simp) with h13452 | h13452
                                        · linarith only [h13160, h13452, hlam]
                                        · rcases p13408_3 (m.d 3 5) (by simp) with h13454 | h13454
                                          · linarith only [h13454, hlam, p13408_0]
                                          · rcases h5bigk with h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c | h13456c
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [hlam, p13456_0]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h10008, hlam, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h13160, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p13166_1, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h11653, h13164, hc34, hc45, hlam, hphi, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h11653, hlam, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [hc15, hlam, hphi, ht01, p13456_1, u0ehi4]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [hlam, p13456_0]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h13155, h13160, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13166_1, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h13158, h13164, hc34, hc45, hlam, hphi, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h13158, hlam, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h11650, hlam, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h13155, hlam, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [hlam, p13456_0]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h10008, h11650, h13158, h13164, hc34, hc45, hlam, hphi, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h13162, hlam, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h11652, hlam, p13456_0]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h13157, hlam, p13456_0]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h13161, hlam, p13456_0]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [hlam, p13456_0]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h13164, hlam, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p13456_1, u0ehi4]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h10008, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p13456_1, u0ehi0]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h13161, h13164, hc34, hc45, hlam, hphi, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [h13164, hc34, hc45, hlam, hphi, p13456_1]
                                            · have p13456_0 := h13456c.1
                                              have p13456_1 := h13456c.2.1
                                              have p13456_2 := h13456c.2.2.1
                                              have p13456_3 := h13456c.2.2.2
                                              linarith only [hlam, p13456_0]
                                      · linarith only [h13451, hlam, p13408_0]
                                    · linarith only [h13157, h13450, hlam]
                                  · linarith only [h11652, h13449, hlam]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h11651, hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h13156, hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h13160, hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h13164, hlam, p13408_1]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h11652, hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h13157, hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h13161, hlam, p13408_0]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [h0, h11648, h13161, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13408_1]
                                · have p13408_0 := h13408c.1
                                  have p13408_1 := h13408c.2.1
                                  have p13408_2 := h13408c.2.2.1
                                  have p13408_3 := h13408c.2.2.2
                                  linarith only [hlam, p13408_0]
                              · linarith only [h13162, h13407, hlam]
                          · linarith only [h13160, h13404, hlam]
                        · linarith only [h0, h11648, h13161, h13403, hlam, p13166_1]
                      · linarith only [h11649, h13402, hlam]
                    · have p13166_0 := h13166c.1
                      have p13166_1 := h13166c.2.1
                      have p13166_2 := h13166c.2.2.1
                      have p13166_3 := h13166c.2.2.2
                      linarith only [hlam, p13166_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h13500 | h13500
                · linarith only [h11649, h11653, h13500, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h13502 | h13502
                  · linarith only [h11653, h13502, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                  · rcases h2bigk with h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c | h13504c
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h0, hlam, p13504_1]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      rcases p13504_3 (m.d 0 2) (by simp) with h13507 | h13507
                      · rcases p13504_3 (m.d 1 2) (by simp) with h13508 | h13508
                        · rcases p13504_3 (m.d 2 3) (by simp) with h13509 | h13509
                          · linarith only [h13509, hlam, p13504_0]
                          · rcases p13504_3 (m.d 2 4) (by simp) with h13511 | h13511
                            · linarith only [h11649, h13511, hlam]
                            · rcases p13504_3 (m.d 2 5) (by simp) with h13513 | h13513
                              · linarith only [h11650, h13513, hlam]
                              · linarith only [h13161, h13513, hlam]
                        · linarith only [h13154, h13508, hlam]
                      · linarith only [h13507, hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      rcases p13504_3 (m.d 0 2) (by simp) with h13518 | h13518
                      · rcases p13504_3 (m.d 1 2) (by simp) with h13519 | h13519
                        · rcases p13504_3 (m.d 2 3) (by simp) with h13520 | h13520
                          · linarith only [h11648, h13520, hlam]
                          · linarith only [h13160, h13520, hlam]
                        · linarith only [h0, h11648, h11652, h13160, h13161, h13519, hlam]
                      · linarith only [h13518, hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      rcases p13504_3 (m.d 0 2) (by simp) with h13525 | h13525
                      · rcases p13504_3 (m.d 1 2) (by simp) with h13526 | h13526
                        · rcases p13504_3 (m.d 2 3) (by simp) with h13527 | h13527
                          · linarith only [h11648, h13527, hlam]
                          · rcases p13504_3 (m.d 2 4) (by simp) with h13529 | h13529
                            · linarith only [h11649, h13529, hlam]
                            · rcases p13504_3 (m.d 2 5) (by simp) with h13531 | h13531
                              · linarith only [h13531, hlam, p13504_0]
                              · rcases h3bigk with h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c | h13533c
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h8410, hlam, p13533_1]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  rcases p13533_3 (m.d 0 3) (by simp) with h13536 | h13536
                                  · rcases p13533_3 (m.d 1 3) (by simp) with h13537 | h13537
                                    · rcases p13533_3 (m.d 2 3) (by simp) with h13538 | h13538
                                      · linarith only [h11648, h13538, hlam]
                                      · rcases p13533_3 (m.d 3 4) (by simp) with h13540 | h13540
                                        · linarith only [h11651, h13540, hlam]
                                        · rcases p13533_3 (m.d 3 5) (by simp) with h13542 | h13542
                                          · linarith only [h11652, h13542, hlam]
                                          · linarith only [h13161, h13542, hlam]
                                    · linarith only [h13154, h13537, hlam]
                                  · linarith only [h11648, h13536, hlam]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h11652, h13160, h13161, hlam, p13533_2]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h0, h11648, h13160, h13161, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13533_1]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h13154, hc12, hlam, hphi, ht01, p13533_1, u0ehi2]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  rcases p13533_3 (m.d 0 3) (by simp) with h13551 | h13551
                                  · linarith only [h13551, h8410, hlam]
                                  · linarith only [h11648, h13551, hlam]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h11652, h13160, h13161, h8410, hlam, p13533_2]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h13160, h13161, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13533_1]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h11648, hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h13154, hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h11652, h13161, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p13533_1]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h13161, hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h11651, hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h13156, hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h13160, hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h13502, hlam, p13533_1]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h11652, hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h13157, hlam, p13533_0]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [h0, h11648, h11652, h13160, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13533_1]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  rcases p13533_3 (m.d 0 3) (by simp) with h13569 | h13569
                                  · rcases p13533_3 (m.d 1 3) (by simp) with h13570 | h13570
                                    · rcases p13533_3 (m.d 2 3) (by simp) with h13571 | h13571
                                      · linarith only [h13161, h13571, hlam]
                                      · linarith only [h13160, h13571, hlam]
                                    · linarith only [h13156, h13570, hlam]
                                  · linarith only [h11651, h13569, hlam]
                                · have p13533_0 := h13533c.1
                                  have p13533_1 := h13533c.2.1
                                  have p13533_2 := h13533c.2.2.1
                                  have p13533_3 := h13533c.2.2.2
                                  linarith only [hlam, p13533_0]
                        · linarith only [h13155, h13526, hlam]
                      · linarith only [h13525, hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [hc12, hlam, hphi, ht01, p13504_1, u0ehi1]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      rcases p13504_3 (m.d 0 2) (by simp) with h13581 | h13581
                      · linarith only [h0, h13581, hlam]
                      · linarith only [h11648, h13581, hlam]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      rcases p13504_3 (m.d 0 2) (by simp) with h13584 | h13584
                      · linarith only [h0, h13584, hlam]
                      · linarith only [h11649, h13584, hlam]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      rcases p13504_3 (m.d 0 2) (by simp) with h13587 | h13587
                      · linarith only [h0, h13587, hlam]
                      · linarith only [h11650, h13587, hlam]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h11648, hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h13154, hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h11648, h11652, h13161, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p13504_1]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h13161, hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h11649, hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h0, h11648, h11652, h13161, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p13504_1]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h13160, hlam, p13504_1]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h13500, hlam, p13504_1]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h11650, hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h13155, hlam, p13504_0]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [h10008, h11650, h13158, h13160, hc34, hc45, hlam, hphi, p13504_1]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      rcases p13504_3 (m.d 0 2) (by simp) with h13603 | h13603
                      · rcases p13504_3 (m.d 1 2) (by simp) with h13604 | h13604
                        · rcases p13504_3 (m.d 2 3) (by simp) with h13605 | h13605
                          · linarith only [h13161, h13605, hlam]
                          · linarith only [h13160, h13605, hlam]
                        · linarith only [h11652, h13154, h13161, h13604, h8410, hlam, p13504_1]
                      · linarith only [h11649, h13603, hlam]
                    · have p13504_0 := h13504c.1
                      have p13504_1 := h13504c.2.1
                      have p13504_2 := h13504c.2.2.1
                      have p13504_3 := h13504c.2.2.2
                      linarith only [hlam, p13504_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h13611 | h13611
              · rcases m.htr 2 4 5 (by decide) (by decide) with h13612 | h13612
                · linarith only [h11651, h11653, h13160, h13611, h13612, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h13160, h13611, h13612, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h13615 | h13615
                · linarith only [h11653, h13615, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h13617 | h13617
                  · linarith only [h10008, h11651, h13158, h13617, hc04, hlam, hphi, u0ehi0]
                  · rcases h2bigk with h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c | h13619c
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [h0, hlam, p13619_1]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      rcases p13619_3 (m.d 0 2) (by simp) with h13622 | h13622
                      · rcases p13619_3 (m.d 1 2) (by simp) with h13623 | h13623
                        · rcases p13619_3 (m.d 2 3) (by simp) with h13624 | h13624
                          · linarith only [h13624, hlam, p13619_0]
                          · rcases p13619_3 (m.d 2 4) (by simp) with h13626 | h13626
                            · linarith only [h11649, h13626, hlam]
                            · linarith only [h13160, h13626, hlam]
                        · linarith only [h13154, h13623, hlam]
                      · linarith only [h13622, hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      rcases p13619_3 (m.d 0 2) (by simp) with h13631 | h13631
                      · rcases p13619_3 (m.d 1 2) (by simp) with h13632 | h13632
                        · rcases p13619_3 (m.d 2 3) (by simp) with h13633 | h13633
                          · linarith only [h11648, h13633, hlam]
                          · rcases p13619_3 (m.d 2 4) (by simp) with h13635 | h13635
                            · linarith only [h13635, hlam, p13619_0]
                            · rcases p13619_3 (m.d 2 5) (by simp) with h13637 | h13637
                              · linarith only [h11650, h13637, hlam]
                              · linarith only [h13615, h13637, hlam]
                        · linarith only [h0, h13632, hlam, p13619_1]
                      · linarith only [h13631, hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      rcases p13619_3 (m.d 0 2) (by simp) with h13642 | h13642
                      · rcases p13619_3 (m.d 1 2) (by simp) with h13643 | h13643
                        · rcases p13619_3 (m.d 2 3) (by simp) with h13644 | h13644
                          · linarith only [h11648, h13644, hlam]
                          · rcases p13619_3 (m.d 2 4) (by simp) with h13646 | h13646
                            · linarith only [h11649, h13646, hlam]
                            · rcases p13619_3 (m.d 2 5) (by simp) with h13648 | h13648
                              · linarith only [h13648, hlam, p13619_0]
                              · rcases h3bigk with h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c | h13650c
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h8410, hlam, p13650_1]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  rcases p13650_3 (m.d 0 3) (by simp) with h13653 | h13653
                                  · rcases p13650_3 (m.d 1 3) (by simp) with h13654 | h13654
                                    · rcases p13650_3 (m.d 2 3) (by simp) with h13655 | h13655
                                      · linarith only [h11648, h13655, hlam]
                                      · rcases p13650_3 (m.d 3 4) (by simp) with h13657 | h13657
                                        · linarith only [h11651, h13657, hlam]
                                        · linarith only [h13160, h13657, hlam]
                                    · linarith only [h13154, h13654, hlam]
                                  · linarith only [h11648, h13653, hlam]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  rcases p13650_3 (m.d 0 3) (by simp) with h13662 | h13662
                                  · rcases p13650_3 (m.d 1 3) (by simp) with h13663 | h13663
                                    · rcases p13650_3 (m.d 2 3) (by simp) with h13664 | h13664
                                      · linarith only [h11648, h13664, hlam]
                                      · rcases p13650_3 (m.d 3 4) (by simp) with h13666 | h13666
                                        · linarith only [h13666, hlam, p13650_0]
                                        · rcases p13650_3 (m.d 3 5) (by simp) with h13668 | h13668
                                          · linarith only [h11652, h13668, hlam]
                                          · linarith only [h13617, h13668, hlam]
                                    · linarith only [h13156, h13663, hlam]
                                  · linarith only [h13662, hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  rcases p13650_3 (m.d 0 3) (by simp) with h13673 | h13673
                                  · rcases p13650_3 (m.d 1 3) (by simp) with h13674 | h13674
                                    · rcases p13650_3 (m.d 2 3) (by simp) with h13675 | h13675
                                      · linarith only [h11648, h13675, hlam]
                                      · rcases p13650_3 (m.d 3 4) (by simp) with h13677 | h13677
                                        · linarith only [h11651, h13677, hlam]
                                        · rcases p13650_3 (m.d 3 5) (by simp) with h13679 | h13679
                                          · linarith only [h13679, hlam, p13650_0]
                                          · rcases h5bigk with h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c | h13681c
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [hlam, p13681_0]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h10008, hlam, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h10008, h13158, h13615, hc24, hc45, hlam, hphi, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h10008, h13158, h13160, h13617, hc23, hc45, hlam, hphi, ht34, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h11653, hlam, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h13158, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p13681_1, u0ehi4]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [hlam, p13681_0]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h11648, h13158, h13160, h13617, hc23, hc45, hlam, hphi, ht34, p13619_2, p13650_1, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h13158, h13160, h13617, hc23, hc45, hlam, hphi, ht34, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h13158, hlam, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h11650, hlam, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h13155, hlam, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [hlam, p13681_0]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h13611, hlam, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h13615, hlam, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h11652, hlam, p13681_0]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h13157, hlam, p13681_0]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h11648, hlam, p13619_2, p13650_1, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [hlam, p13681_0]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h13617, hlam, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h0, h10008, h11648, h13160, h13617, hc12, hc23, hc45, hlam, hphi, ht01, ht34, p13650_1, p13681_1, u0ehi0]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h0, h10008, h11648, h13160, h13617, hc12, hc23, hc45, hlam, hphi, ht01, ht34, p13650_1, p13681_1, u0ehi0]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h11648, h13160, h13617, hc23, hc45, hlam, hphi, ht34, p13619_2, p13650_1, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [h13160, h13617, hc23, hc45, hlam, hphi, ht34, p13681_1]
                                            · have p13681_0 := h13681c.1
                                              have p13681_1 := h13681c.2.1
                                              have p13681_2 := h13681c.2.2.1
                                              have p13681_3 := h13681c.2.2.2
                                              linarith only [hlam, p13681_0]
                                    · linarith only [h13157, h13674, hlam]
                                  · linarith only [h13673, hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h13154, hc12, hlam, hphi, ht01, p13650_1, u0ehi2]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  rcases p13650_3 (m.d 0 3) (by simp) with h13711 | h13711
                                  · linarith only [h13711, h8410, hlam]
                                  · linarith only [h11648, h13711, hlam]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  rcases p13650_3 (m.d 0 3) (by simp) with h13714 | h13714
                                  · linarith only [h13714, h8410, hlam]
                                  · linarith only [h11651, h13714, hlam]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  rcases p13650_3 (m.d 0 3) (by simp) with h13717 | h13717
                                  · linarith only [h13717, h8410, hlam]
                                  · linarith only [h11652, h13717, hlam]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h11648, hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h13154, hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h13160, hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h13611, hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h11651, hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h13156, hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h11651, h11653, hc23, hc45, hlam, hphi, ht34, p13650_1]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h13617, hlam, p13650_1]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h11652, hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h13157, hlam, p13650_0]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  rcases p13650_3 (m.d 0 3) (by simp) with h13732 | h13732
                                  · rcases p13650_3 (m.d 1 3) (by simp) with h13733 | h13733
                                    · rcases p13650_3 (m.d 2 3) (by simp) with h13734 | h13734
                                      · linarith only [h13734, hlam, p13650_0]
                                      · rcases p13650_3 (m.d 3 4) (by simp) with h13736 | h13736
                                        · linarith only [h13617, h13736, hlam]
                                        · linarith only [h13160, h13736, hlam]
                                    · linarith only [h13154, h13733, hlam]
                                  · linarith only [h11648, h13732, hlam]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [h11648, h11652, h13160, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13650_1]
                                · have p13650_0 := h13650c.1
                                  have p13650_1 := h13650c.2.1
                                  have p13650_2 := h13650c.2.2.1
                                  have p13650_3 := h13650c.2.2.2
                                  linarith only [hlam, p13650_0]
                        · linarith only [h13155, h13643, hlam]
                      · linarith only [h13642, hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [hc12, hlam, hphi, ht01, p13619_1, u0ehi1]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      rcases p13619_3 (m.d 0 2) (by simp) with h13747 | h13747
                      · linarith only [h0, h13747, hlam]
                      · linarith only [h11648, h13747, hlam]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      rcases p13619_3 (m.d 0 2) (by simp) with h13750 | h13750
                      · linarith only [h0, h13750, hlam]
                      · linarith only [h11649, h13750, hlam]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      rcases p13619_3 (m.d 0 2) (by simp) with h13753 | h13753
                      · linarith only [h0, h13753, hlam]
                      · linarith only [h11650, h13753, hlam]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [h11648, hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [h13154, hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [h13160, hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [h13611, hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [h11649, hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [h0, hc24, hlam, hphi, ht01, ht12, p13619_1, u0ehi0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [h11651, h11653, h13160, hc23, hc45, hlam, hphi, ht34, p13619_1]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [h13615, hlam, p13619_1]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [h11650, hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [h13155, hlam, p13619_0]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      rcases p13619_3 (m.d 0 2) (by simp) with h13768 | h13768
                      · rcases p13619_3 (m.d 1 2) (by simp) with h13769 | h13769
                        · rcases p13619_3 (m.d 2 3) (by simp) with h13770 | h13770
                          · linarith only [h13611, h13770, hlam]
                          · rcases p13619_3 (m.d 2 4) (by simp) with h13772 | h13772
                            · linarith only [h13615, h13772, hlam]
                            · linarith only [h13160, h13772, hlam]
                        · linarith only [h13154, h13769, hlam]
                      · linarith only [h11648, h13768, hlam]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      rcases p13619_3 (m.d 0 2) (by simp) with h13777 | h13777
                      · rcases p13619_3 (m.d 1 2) (by simp) with h13778 | h13778
                        · rcases p13619_3 (m.d 2 3) (by simp) with h13779 | h13779
                          · linarith only [h13611, h13779, hlam]
                          · rcases p13619_3 (m.d 2 4) (by simp) with h13781 | h13781
                            · linarith only [h13615, h13781, hlam]
                            · rcases p13619_3 (m.d 2 5) (by simp) with h13783 | h13783
                              · rcases h3bigk with h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c | h13784c
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h8410, hlam, p13784_1]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h11652, h13160, h13611, hlam, p13619_1, p13784_2]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  rcases p13784_3 (m.d 0 3) (by simp) with h13788 | h13788
                                  · rcases p13784_3 (m.d 1 3) (by simp) with h13789 | h13789
                                    · rcases p13784_3 (m.d 2 3) (by simp) with h13790 | h13790
                                      · linarith only [h11648, h13790, hlam]
                                      · rcases p13784_3 (m.d 3 4) (by simp) with h13792 | h13792
                                        · linarith only [h13792, hlam, p13784_0]
                                        · rcases p13784_3 (m.d 3 5) (by simp) with h13794 | h13794
                                          · linarith only [h11652, h13794, hlam]
                                          · linarith only [h13617, h13794, hlam]
                                    · linarith only [h13156, h13789, hlam]
                                  · linarith only [h13788, hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h13160, h13611, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13619_1, p13784_1]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [hc13, hlam, hphi, ht01, p13784_1, u0ehi2]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h11652, h13160, h13611, h8410, hlam, p13619_1, p13784_2]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  rcases p13784_3 (m.d 0 3) (by simp) with h13803 | h13803
                                  · linarith only [h13803, h8410, hlam]
                                  · linarith only [h11651, h13803, hlam]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h13160, h13611, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13619_1, p13784_1]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h11648, hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h13154, hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h13160, hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h13611, hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h11651, hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h13156, hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h11651, h11653, hc23, hc45, hlam, hphi, ht34, p13784_1]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h13617, hlam, p13784_1]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h11652, hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h13157, hlam, p13784_0]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  rcases p13784_3 (m.d 0 3) (by simp) with h13819 | h13819
                                  · rcases p13784_3 (m.d 1 3) (by simp) with h13820 | h13820
                                    · rcases p13784_3 (m.d 2 3) (by simp) with h13821 | h13821
                                      · linarith only [h13821, hlam, p13784_0]
                                      · rcases p13784_3 (m.d 3 4) (by simp) with h13823 | h13823
                                        · linarith only [h13617, h13823, hlam]
                                        · linarith only [h13160, h13823, hlam]
                                    · linarith only [h13154, h13820, hlam]
                                  · linarith only [h11648, h13819, hlam]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [h11652, h13160, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13784_1]
                                · have p13784_0 := h13784c.1
                                  have p13784_1 := h13784c.2.1
                                  have p13784_2 := h13784c.2.2.1
                                  have p13784_3 := h13784c.2.2.2
                                  linarith only [hlam, p13784_0]
                              · linarith only [h13615, h13783, hlam]
                        · linarith only [h0, h13778, hc25, hlam, hphi, ht01, ht12, p13619_1, u0ehi1]
                      · linarith only [h11649, h13777, hlam]
                    · have p13619_0 := h13619c.1
                      have p13619_1 := h13619c.2.1
                      have p13619_2 := h13619c.2.2.1
                      have p13619_3 := h13619c.2.2.2
                      linarith only [hlam, p13619_0]
        · linarith only [h11648, h11652, h13157, h8410, hc02, hlam, hphi, u0ehi0]
      · linarith only [h11651, h13156, h8410, hc04, hlam, hphi, u0ehi0]
    · linarith only [h0, h11650, h11652, h13155, hc03, hlam, hphi, u0ehi0]
  · linarith only [h0, h13154, hc23, hlam, hphi, ht01, ht12, u0ehi0]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11650 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11651 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11652 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 0 4 5 (by decide) (by decide) with h11653 | h11653
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649 h11650 h11651 h11652 h11653
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649 h11650 h11651 h11652 h11653

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11650 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11651 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11652 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 0 4 5 (by decide) (by decide) with h13838 | h13838
  · linarith only [h11651, h11652, h13838, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h13840 | h13840
    · rcases m.htr 1 2 5 (by decide) (by decide) with h13841 | h13841
      · rcases m.htr 1 3 4 (by decide) (by decide) with h13842 | h13842
        · rcases m.htr 1 3 5 (by decide) (by decide) with h13843 | h13843
          · linarith only [h11652, h13840, h13843, hc12, hlam, hphi, ht01, u0ehi2]
          · linarith only [h13843, h8410, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
        · linarith only [h11651, h13842, h8410, hc03, hlam, hphi, u0ehi0]
      · linarith only [h0, h11650, h13841, hc02, hlam, hphi, u0ehi0]
    · linarith only [h0, h11648, h11652, h13840, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11650 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11651 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 0 3 5 (by decide) (by decide) with h11652 | h11652
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649 h11650 h11651 h11652
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649 h11650 h11651 h11652

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11650 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11651 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 0 3 5 (by decide) (by decide) with h13849 | h13849
  · rcases m.htr 0 4 5 (by decide) (by decide) with h13850 | h13850
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13851 | h13851
      · rcases m.htr 1 2 5 (by decide) (by decide) with h13852 | h13852
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13853 | h13853
          · linarith only [h10008, h11651, h13849, h13851, h13853, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h13853, h8410, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
        · linarith only [h0, h11650, h13852, hc02, hlam, hphi, u0ehi0]
      · linarith only [h0, h11648, h11651, h13851, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
    · linarith only [h11651, h13849, h13850, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h13859 | h13859
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13860 | h13860
      · rcases m.htr 1 2 5 (by decide) (by decide) with h13861 | h13861
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13862 | h13862
          · linarith only [h11651, h13860, h13862, h8410, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h13862, h8410, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
        · linarith only [h0, h11650, h13861, hc02, hlam, hphi, u0ehi0]
      · linarith only [h0, h11648, h13849, h13860, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13867 | h13867
      · rcases m.htr 1 2 5 (by decide) (by decide) with h13868 | h13868
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13869 | h13869
          · linarith only [h11651, h13867, h13869, h8410, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h13869, h8410, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
        · linarith only [h0, h11650, h13868, hc02, hlam, hphi, u0ehi0]
      · linarith only [h0, h11648, h11651, h13859, h13867, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11650 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 0 3 4 (by decide) (by decide) with h11651 | h11651
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649 h11650 h11651
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649 h11650 h11651

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11650 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 0 3 4 (by decide) (by decide) with h13874 | h13874
  · rcases m.htr 0 3 5 (by decide) (by decide) with h13875 | h13875
    · linarith only [h11648, h11650, h13875, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h13877 | h13877
      · linarith only [h11649, h11650, h13877, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h13879 | h13879
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13880 | h13880
          · linarith only [h11648, h11650, h13880, h8410, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h13880, hc25, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h11648, h13879, hc02, hlam, hphi, u0ehi0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h13884 | h13884
    · linarith only [h11648, h11650, h13884, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h13886 | h13886
      · linarith only [h11649, h11650, h13886, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h13888 | h13888
        · rcases m.htr 1 2 5 (by decide) (by decide) with h13889 | h13889
          · linarith only [h11649, h11650, h13874, h13889, h8410, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h13889, hc25, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h11648, h13888, hc02, hlam, hphi, u0ehi0]

end R2N4
