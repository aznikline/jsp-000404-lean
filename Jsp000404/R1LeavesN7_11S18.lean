import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h11188 | h11188
  · rcases m.htr 1 2 5 (by decide) (by decide) with h11189 | h11189
    · rcases m.htr 1 3 4 (by decide) (by decide) with h11190 | h11190
      · rcases m.htr 1 3 5 (by decide) (by decide) with h11191 | h11191
        · rcases m.htr 1 4 5 (by decide) (by decide) with h11192 | h11192
          · linarith only [h10014, h11192, hc14, hlam, hphi, ht01, u0ehi3]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h11194 | h11194
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11195 | h11195
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11196 | h11196
                · linarith only [h10014, h11196, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11198 | h11198
                  · linarith only [h10009, h10014, h11194, h11198, hc02, hlam, hphi, u0ehi3]
                  · rcases h2bigk with h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c | h11200c
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [h0, hlam, p11200_1]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      rcases p11200_3 (m.d 0 2) (by simp) with h11203 | h11203
                      · rcases p11200_3 (m.d 1 2) (by simp) with h11204 | h11204
                        · rcases p11200_3 (m.d 2 3) (by simp) with h11205 | h11205
                          · linarith only [h11205, hlam, p11200_0]
                          · rcases p11200_3 (m.d 2 4) (by simp) with h11207 | h11207
                            · linarith only [h10010, h11207, hlam]
                            · rcases p11200_3 (m.d 2 5) (by simp) with h11209 | h11209
                              · linarith only [h10011, h11209, hlam]
                              · rcases h3bigk with h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c | h11211c
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h8410, hlam, p11211_1]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  rcases p11211_3 (m.d 0 3) (by simp) with h11214 | h11214
                                  · rcases p11211_3 (m.d 1 3) (by simp) with h11215 | h11215
                                    · rcases p11211_3 (m.d 2 3) (by simp) with h11216 | h11216
                                      · linarith only [h10009, h11216, hlam]
                                      · rcases p11211_3 (m.d 3 4) (by simp) with h11218 | h11218
                                        · linarith only [h10012, h11218, hlam]
                                        · rcases p11211_3 (m.d 3 5) (by simp) with h11220 | h11220
                                          · linarith only [h10013, h11220, hlam]
                                          · rcases h5bigk with h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c | h11222c
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [hlam, p11222_0]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h0, h10008, h11189, h11196, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h0, h10008, h11196, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h0, h10008, h11198, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h10014, hlam, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h10008, hlam, p11222_0]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [hlam, p11222_0]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h0, h10008, h11196, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h10008, h11188, h11198, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h11192, hlam, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h10011, hlam, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h11189, hlam, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [hlam, p11222_0]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h0, h10011, h11198, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h11196, hlam, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h10013, hlam, p11222_0]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h11191, hlam, p11222_0]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h11195, hlam, p11222_0]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [hlam, p11222_0]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h11198, hlam, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p11222_1, u0ehi4]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h11191, h11198, hc34, hc45, hlam, hphi, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h11195, h11198, hc34, hc45, hlam, hphi, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [h11198, hc34, hc45, hlam, hphi, p11222_1]
                                            · have p11222_0 := h11222c.1
                                              have p11222_1 := h11222c.2.1
                                              have p11222_2 := h11222c.2.2.1
                                              have p11222_3 := h11222c.2.2.2
                                              linarith only [hlam, p11222_0]
                                    · linarith only [h11188, h11215, hlam]
                                  · linarith only [h10009, h11214, hlam]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  rcases p11211_3 (m.d 0 3) (by simp) with h11250 | h11250
                                  · rcases p11211_3 (m.d 1 3) (by simp) with h11251 | h11251
                                    · rcases p11211_3 (m.d 2 3) (by simp) with h11252 | h11252
                                      · linarith only [h10009, h11252, hlam]
                                      · linarith only [h11194, h11252, hlam]
                                    · linarith only [h11190, h11251, hlam]
                                  · linarith only [h11250, hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  rcases p11211_3 (m.d 0 3) (by simp) with h11257 | h11257
                                  · rcases p11211_3 (m.d 1 3) (by simp) with h11258 | h11258
                                    · rcases p11211_3 (m.d 2 3) (by simp) with h11259 | h11259
                                      · linarith only [h10009, h11259, hlam]
                                      · linarith only [h11195, h11259, hlam]
                                    · linarith only [h11191, h11258, hlam]
                                  · linarith only [h11257, hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h11188, hc12, hlam, hphi, ht01, p11211_1, u0ehi2]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  rcases p11211_3 (m.d 0 3) (by simp) with h11266 | h11266
                                  · linarith only [h11266, h8410, hlam]
                                  · linarith only [h10009, h11266, hlam]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  rcases p11211_3 (m.d 0 3) (by simp) with h11269 | h11269
                                  · linarith only [h11269, h8410, hlam]
                                  · linarith only [h10012, h11269, hlam]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  rcases p11211_3 (m.d 0 3) (by simp) with h11272 | h11272
                                  · linarith only [h11272, h8410, hlam]
                                  · linarith only [h10013, h11272, hlam]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h10009, hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h11188, hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11200_1, p11211_1]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p11200_1, p11211_1]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h10012, hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h11190, hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h11194, hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h11198, hlam, p11211_1]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h10013, hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h11191, hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h11195, hlam, p11211_0]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [h10008, h11191, h8410, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11211_1]
                                · have p11211_0 := h11211c.1
                                  have p11211_1 := h11211c.2.1
                                  have p11211_2 := h11211c.2.2.1
                                  have p11211_3 := h11211c.2.2.2
                                  linarith only [hlam, p11211_0]
                        · linarith only [h11188, h11204, hlam]
                      · linarith only [h11203, hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      rcases p11200_3 (m.d 0 2) (by simp) with h11292 | h11292
                      · rcases p11200_3 (m.d 1 2) (by simp) with h11293 | h11293
                        · rcases p11200_3 (m.d 2 3) (by simp) with h11294 | h11294
                          · linarith only [h10009, h11294, hlam]
                          · linarith only [h11194, h11294, hlam]
                        · linarith only [h0, h11293, hlam, p11200_1]
                      · linarith only [h11292, hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      rcases p11200_3 (m.d 0 2) (by simp) with h11299 | h11299
                      · rcases p11200_3 (m.d 1 2) (by simp) with h11300 | h11300
                        · rcases p11200_3 (m.d 2 3) (by simp) with h11301 | h11301
                          · linarith only [h10009, h11301, hlam]
                          · linarith only [h11195, h11301, hlam]
                        · linarith only [h11189, h11300, hlam]
                      · linarith only [h11299, hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [hc12, hlam, hphi, ht01, p11200_1, u0ehi1]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      rcases p11200_3 (m.d 0 2) (by simp) with h11308 | h11308
                      · linarith only [h0, h11308, hlam]
                      · linarith only [h10009, h11308, hlam]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      rcases p11200_3 (m.d 0 2) (by simp) with h11311 | h11311
                      · linarith only [h0, h11311, hlam]
                      · linarith only [h10010, h11311, hlam]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      rcases p11200_3 (m.d 0 2) (by simp) with h11314 | h11314
                      · linarith only [h0, h11314, hlam]
                      · linarith only [h10011, h11314, hlam]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [h10009, hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [h11188, hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      rcases p11200_3 (m.d 0 2) (by simp) with h11320 | h11320
                      · rcases p11200_3 (m.d 1 2) (by simp) with h11321 | h11321
                        · rcases p11200_3 (m.d 2 3) (by simp) with h11322 | h11322
                          · rcases p11200_3 (m.d 2 4) (by simp) with h11323 | h11323
                            · linarith only [h11194, h11323, hlam]
                            · rcases p11200_3 (m.d 2 5) (by simp) with h11325 | h11325
                              · linarith only [h11195, h11325, hlam]
                              · linarith only [h11196, h11325, hlam]
                          · linarith only [h11194, h11322, hlam]
                        · linarith only [h10009, h11188, h11321, h8410, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11200_1]
                      · linarith only [h10010, h11320, hlam]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      rcases p11200_3 (m.d 0 2) (by simp) with h11331 | h11331
                      · rcases p11200_3 (m.d 1 2) (by simp) with h11332 | h11332
                        · rcases p11200_3 (m.d 2 3) (by simp) with h11333 | h11333
                          · rcases p11200_3 (m.d 2 4) (by simp) with h11334 | h11334
                            · linarith only [h11194, h11334, hlam]
                            · rcases p11200_3 (m.d 2 5) (by simp) with h11336 | h11336
                              · linarith only [h11195, h11336, hlam]
                              · rcases h3bigk with h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c | h11338c
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h8410, hlam, p11338_1]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h11195, h11198, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11200_1, p11338_1]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  rcases p11338_3 (m.d 0 3) (by simp) with h11342 | h11342
                                  · rcases p11338_3 (m.d 1 3) (by simp) with h11343 | h11343
                                    · rcases p11338_3 (m.d 2 3) (by simp) with h11344 | h11344
                                      · linarith only [h10009, h11344, hlam]
                                      · linarith only [h11194, h11344, hlam]
                                    · linarith only [h11190, h11343, hlam]
                                  · linarith only [h11342, hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  rcases p11338_3 (m.d 0 3) (by simp) with h11349 | h11349
                                  · rcases p11338_3 (m.d 1 3) (by simp) with h11350 | h11350
                                    · rcases p11338_3 (m.d 2 3) (by simp) with h11351 | h11351
                                      · linarith only [h10009, h11351, hlam]
                                      · linarith only [h11195, h11351, hlam]
                                    · linarith only [h11191, h11350, hlam]
                                  · linarith only [h11349, hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h11188, hc12, hlam, hphi, ht01, p11338_1, u0ehi2]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h11188, h11195, h11198, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11200_1, p11338_1]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  rcases p11338_3 (m.d 0 3) (by simp) with h11359 | h11359
                                  · linarith only [h11359, h8410, hlam]
                                  · linarith only [h10012, h11359, hlam]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  rcases p11338_3 (m.d 0 3) (by simp) with h11362 | h11362
                                  · linarith only [h11362, h8410, hlam]
                                  · linarith only [h10013, h11362, hlam]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h10009, hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h11188, hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  rcases p11338_3 (m.d 0 3) (by simp) with h11368 | h11368
                                  · rcases p11338_3 (m.d 1 3) (by simp) with h11369 | h11369
                                    · rcases p11338_3 (m.d 2 3) (by simp) with h11370 | h11370
                                      · rcases p11338_3 (m.d 3 4) (by simp) with h11371 | h11371
                                        · linarith only [h11371, hlam, p11338_0]
                                        · rcases p11338_3 (m.d 3 5) (by simp) with h11373 | h11373
                                          · linarith only [h11195, h11373, hlam]
                                          · linarith only [h11198, h11373, hlam]
                                      · linarith only [h11370, hlam, p11338_0]
                                    · linarith only [h11190, h11369, hlam]
                                  · linarith only [h10012, h11368, hlam]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  rcases p11338_3 (m.d 0 3) (by simp) with h11379 | h11379
                                  · rcases p11338_3 (m.d 1 3) (by simp) with h11380 | h11380
                                    · rcases p11338_3 (m.d 2 3) (by simp) with h11381 | h11381
                                      · rcases p11338_3 (m.d 3 4) (by simp) with h11382 | h11382
                                        · linarith only [h11194, h11382, hlam]
                                        · rcases p11338_3 (m.d 3 5) (by simp) with h11384 | h11384
                                          · linarith only [h11384, hlam, p11338_0]
                                          · rcases h5bigk with h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c | h11386c
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [hlam, p11386_0]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h10008, h8410, hc13, hc15, hlam, hphi, ht01, ht0b, ht5b, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h10008, h11195, h11198, h8410, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h10008, h11198, h8410, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h10014, hlam, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h10008, hlam, p11386_0]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [hlam, p11386_0]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h10008, h11188, h11195, h11198, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h10008, h11188, h11198, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h11192, hlam, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h10011, hlam, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h11189, hlam, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [hlam, p11386_0]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h0, h10011, h11198, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h11196, hlam, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h10013, hlam, p11386_0]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h11191, hlam, p11386_0]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h11195, hlam, p11386_0]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [hlam, p11386_0]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h11198, hlam, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p11386_1, u0ehi4]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h11191, h11198, hc34, hc45, hlam, hphi, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h11195, h11198, hc34, hc45, hlam, hphi, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [h11198, hc34, hc45, hlam, hphi, p11386_1]
                                            · have p11386_0 := h11386c.1
                                              have p11386_1 := h11386c.2.1
                                              have p11386_2 := h11386c.2.2.1
                                              have p11386_3 := h11386c.2.2.2
                                              linarith only [hlam, p11386_0]
                                      · linarith only [h11381, hlam, p11338_0]
                                    · linarith only [h11191, h11380, hlam]
                                  · linarith only [h10013, h11379, hlam]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h10012, hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h11190, hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h11194, hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h11198, hlam, p11338_1]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h10013, hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h11191, hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h11195, hlam, p11338_0]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [h0, h10009, h11195, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11200_1, p11338_1]
                                · have p11338_0 := h11338c.1
                                  have p11338_1 := h11338c.2.1
                                  have p11338_2 := h11338c.2.2.1
                                  have p11338_3 := h11338c.2.2.2
                                  linarith only [hlam, p11338_0]
                          · linarith only [h11195, h11333, hlam]
                        · linarith only [h11189, h11332, hlam]
                      · linarith only [h10011, h11331, hlam]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [h10010, hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [h11188, h8410, hc01, hc24, hlam, hphi, ht12, p11200_1]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [h11194, hlam, p11200_1]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [h11196, hlam, p11200_1]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [h10011, hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [h11189, hlam, p11200_0]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [h11195, hlam, p11200_1]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [h10008, h11189, h8410, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11200_1]
                    · have p11200_0 := h11200c.1
                      have p11200_1 := h11200c.2.1
                      have p11200_2 := h11200c.2.2.1
                      have p11200_3 := h11200c.2.2.2
                      linarith only [hlam, p11200_0]
              · linarith only [h10008, h11188, h11191, h11194, h11195, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11439 | h11439
              · linarith only [h10008, h11188, h11190, h11192, h11194, h11439, h8410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11441 | h11441
                · linarith only [h10014, h11441, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11443 | h11443
                  · linarith only [h10008, h10014, h11188, h11190, h11192, h11443, h8410, hc12, hlam, hphi, ht01, u0ehi3]
                  · rcases h2bigk with h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c | h11445c
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h0, hlam, p11445_1]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      rcases p11445_3 (m.d 0 2) (by simp) with h11448 | h11448
                      · rcases p11445_3 (m.d 1 2) (by simp) with h11449 | h11449
                        · rcases p11445_3 (m.d 2 3) (by simp) with h11450 | h11450
                          · linarith only [h11450, hlam, p11445_0]
                          · rcases p11445_3 (m.d 2 4) (by simp) with h11452 | h11452
                            · linarith only [h10010, h11452, hlam]
                            · linarith only [h11194, h11452, hlam]
                        · linarith only [h11188, h11449, hlam]
                      · linarith only [h11448, hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      rcases p11445_3 (m.d 0 2) (by simp) with h11457 | h11457
                      · rcases p11445_3 (m.d 1 2) (by simp) with h11458 | h11458
                        · rcases p11445_3 (m.d 2 3) (by simp) with h11459 | h11459
                          · linarith only [h10009, h11459, hlam]
                          · rcases p11445_3 (m.d 2 4) (by simp) with h11461 | h11461
                            · linarith only [h11461, hlam, p11445_0]
                            · rcases p11445_3 (m.d 2 5) (by simp) with h11463 | h11463
                              · linarith only [h10011, h11463, hlam]
                              · linarith only [h11441, h11463, hlam]
                        · linarith only [h10008, h11188, h11190, h11192, h11194, h11458, h8410, hlam]
                      · linarith only [h11457, hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      rcases p11445_3 (m.d 0 2) (by simp) with h11468 | h11468
                      · rcases p11445_3 (m.d 1 2) (by simp) with h11469 | h11469
                        · rcases p11445_3 (m.d 2 3) (by simp) with h11470 | h11470
                          · linarith only [h10009, h11470, hlam]
                          · rcases p11445_3 (m.d 2 4) (by simp) with h11472 | h11472
                            · linarith only [h10010, h11472, hlam]
                            · rcases p11445_3 (m.d 2 5) (by simp) with h11474 | h11474
                              · linarith only [h11474, hlam, p11445_0]
                              · rcases h3bigk with h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c | h11476c
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h8410, hlam, p11476_1]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  rcases p11476_3 (m.d 0 3) (by simp) with h11479 | h11479
                                  · rcases p11476_3 (m.d 1 3) (by simp) with h11480 | h11480
                                    · rcases p11476_3 (m.d 2 3) (by simp) with h11481 | h11481
                                      · linarith only [h10009, h11481, hlam]
                                      · rcases p11476_3 (m.d 3 4) (by simp) with h11483 | h11483
                                        · linarith only [h10012, h11483, hlam]
                                        · linarith only [h11194, h11483, hlam]
                                    · linarith only [h11188, h11480, hlam]
                                  · linarith only [h10009, h11479, hlam]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  rcases p11476_3 (m.d 0 3) (by simp) with h11488 | h11488
                                  · rcases p11476_3 (m.d 1 3) (by simp) with h11489 | h11489
                                    · rcases p11476_3 (m.d 2 3) (by simp) with h11490 | h11490
                                      · linarith only [h10009, h11490, hlam]
                                      · rcases p11476_3 (m.d 3 4) (by simp) with h11492 | h11492
                                        · linarith only [h11492, hlam, p11476_0]
                                        · rcases p11476_3 (m.d 3 5) (by simp) with h11494 | h11494
                                          · linarith only [h10013, h11494, hlam]
                                          · linarith only [h11443, h11494, hlam]
                                    · linarith only [h11190, h11489, hlam]
                                  · linarith only [h11488, hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  rcases p11476_3 (m.d 0 3) (by simp) with h11499 | h11499
                                  · rcases p11476_3 (m.d 1 3) (by simp) with h11500 | h11500
                                    · rcases p11476_3 (m.d 2 3) (by simp) with h11501 | h11501
                                      · linarith only [h10009, h11501, hlam]
                                      · rcases p11476_3 (m.d 3 4) (by simp) with h11503 | h11503
                                        · linarith only [h10012, h11503, hlam]
                                        · rcases p11476_3 (m.d 3 5) (by simp) with h11505 | h11505
                                          · linarith only [h11505, hlam, p11476_0]
                                          · rcases h5bigk with h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c | h11507c
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [hlam, p11507_0]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10008, h11188, h11190, h11192, h11194, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10008, h11188, h11441, h8410, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10008, h11188, h11194, h11443, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10014, hlam, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10008, hlam, p11507_0]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [hlam, p11507_0]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10008, h10009, h11188, h11194, h11443, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11445_2, p11476_1, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10008, h11188, h11194, h11443, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h11192, hlam, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10011, hlam, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h11189, hlam, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [hlam, p11507_0]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h11439, hlam, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h11441, hlam, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10013, hlam, p11507_0]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h11191, hlam, p11507_0]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10009, hlam, p11445_2, p11476_1, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [hlam, p11507_0]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h11443, hlam, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p11507_1, u0ehi4]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10009, h11189, h11194, h11443, hc23, hc45, hlam, hphi, ht34, p11445_2, p11476_1, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h10009, h11194, h11443, hc23, hc45, hlam, hphi, ht34, p11445_2, p11476_1, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [h11194, h11443, hc23, hc45, hlam, hphi, ht34, p11507_1]
                                            · have p11507_0 := h11507c.1
                                              have p11507_1 := h11507c.2.1
                                              have p11507_2 := h11507c.2.2.1
                                              have p11507_3 := h11507c.2.2.2
                                              linarith only [hlam, p11507_0]
                                    · linarith only [h11191, h11500, hlam]
                                  · linarith only [h11499, hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h11188, hc12, hlam, hphi, ht01, p11476_1, u0ehi2]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h10008, h11191, h11194, h11443, h8410, hlam, p11476_2]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  rcases p11476_3 (m.d 0 3) (by simp) with h11538 | h11538
                                  · linarith only [h11538, h8410, hlam]
                                  · linarith only [h10012, h11538, hlam]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  rcases p11476_3 (m.d 0 3) (by simp) with h11541 | h11541
                                  · linarith only [h11541, h8410, hlam]
                                  · linarith only [h10013, h11541, hlam]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h10009, hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h11188, hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h11194, hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h11439, hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h10012, hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h11190, hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h10008, h11191, h11443, h8410, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11476_1]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h11443, hlam, p11476_1]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h10013, hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h11191, hlam, p11476_0]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h10008, h11188, h11191, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11476_1]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [h10008, h11188, h11191, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11476_1]
                                · have p11476_0 := h11476c.1
                                  have p11476_1 := h11476c.2.1
                                  have p11476_2 := h11476c.2.2.1
                                  have p11476_3 := h11476c.2.2.2
                                  linarith only [hlam, p11476_0]
                        · linarith only [h11189, h11469, hlam]
                      · linarith only [h11468, hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h10009, h8410, hc12, hlam, hphi, ht01, p11445_1, u0ehi0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h10008, h11188, h11190, h11192, h11194, h8410, hlam, p11445_2]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      rcases p11445_3 (m.d 0 2) (by simp) with h11564 | h11564
                      · linarith only [h0, h11564, hlam]
                      · linarith only [h10010, h11564, hlam]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      rcases p11445_3 (m.d 0 2) (by simp) with h11567 | h11567
                      · linarith only [h0, h11567, hlam]
                      · linarith only [h10011, h11567, hlam]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h10009, hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h11188, hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h11194, hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h11439, hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h10010, hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h10008, h11188, h11190, h11192, h11194, h8410, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11445_1]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h10008, h11190, h11192, h11194, h8410, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11445_1]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h11441, hlam, p11445_1]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h10011, hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h11189, hlam, p11445_0]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h10008, h11188, h11191, h11439, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11445_1]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [h10008, h11188, h11191, h11439, h8410, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11445_1]
                    · have p11445_0 := h11445c.1
                      have p11445_1 := h11445c.2.1
                      have p11445_2 := h11445c.2.2.1
                      have p11445_3 := h11445c.2.2.2
                      linarith only [hlam, p11445_0]
        · linarith only [h11191, h8410, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
      · linarith only [h10008, h10014, h11190, h8410, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
    · linarith only [h10008, h10014, h11188, h11189, h8410, hc25, hlam, hphi, ht01, ht12, u0ehi3]
  · linarith only [h0, h10008, h10014, h11188, hc23, hlam, hphi, ht01, ht12, u0ehi3]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h10014 | h10014
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  linarith only [h10008, h10013, h8410, hlam]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h10013 | h10013
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h11590 | h11590
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11591 | h11591
    · rcases m.htr 1 2 3 (by decide) (by decide) with h11592 | h11592
      · rcases m.htr 1 2 5 (by decide) (by decide) with h11593 | h11593
        · rcases m.htr 1 3 4 (by decide) (by decide) with h11594 | h11594
          · linarith only [h10012, h11592, h11594, h8410, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h10008, h11594, h8410, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
        · linarith only [h0, h10008, h11593, hc25, hlam, hphi, ht01, ht12, u0ehi4]
      · linarith only [h0, h10008, h10009, h11592, hc02, hlam, hphi, u0ehi4]
    · linarith only [h10008, h10012, h11591, h8410, hlam]
  · linarith only [h10008, h11590, h8410, hlam]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h10012 | h10012
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  linarith only [h0, h10008, h10011, hlam]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h10011 | h10011
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h11602 | h11602
  · rcases m.htr 0 3 4 (by decide) (by decide) with h11603 | h11603
    · linarith only [h10009, h10010, h11603, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h11605 | h11605
      · rcases m.htr 0 4 5 (by decide) (by decide) with h11606 | h11606
        · rcases m.htr 1 2 3 (by decide) (by decide) with h11607 | h11607
          · rcases m.htr 1 2 5 (by decide) (by decide) with h11608 | h11608
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11609 | h11609
              · linarith only [h10008, h11603, h11609, h8410, hc13, hlam, hphi, ht01, u0ehi4]
              · linarith only [h10008, h11609, h8410, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
            · linarith only [h0, h10008, h11608, hc25, hlam, hphi, ht01, ht12, u0ehi4]
          · linarith only [h0, h10008, h10009, h11607, hc02, hlam, hphi, u0ehi4]
        · linarith only [h0, h10008, h10010, h11606, hlam]
      · linarith only [h10008, h11605, h8410, hlam]
  · linarith only [h10008, h10009, h11602, h8410, hlam]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h10010 | h10010
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h11617 | h11617
  · rcases m.htr 0 2 5 (by decide) (by decide) with h11618 | h11618
    · rcases m.htr 0 3 4 (by decide) (by decide) with h11619 | h11619
      · rcases m.htr 0 3 5 (by decide) (by decide) with h11620 | h11620
        · rcases m.htr 0 4 5 (by decide) (by decide) with h11621 | h11621
          · rcases m.htr 1 2 3 (by decide) (by decide) with h11622 | h11622
            · linarith only [h10009, h11622, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h10008, h11622, hc23, hlam, hphi, ht01, ht12, u0ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h11625 | h11625
            · linarith only [h0, h10008, h10009, h11621, h11625, hc12, hlam, hphi, ht01, u0ehi3]
            · linarith only [h0, h10008, h11621, h11625, hc23, hlam, hphi, ht01, ht12, u0ehi3]
        · linarith only [h0, h10008, h10009, h11620, hlam]
      · linarith only [h10009, h11617, h11619, hlam]
    · linarith only [h0, h10008, h11618, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h11631 | h11631
    · rcases m.htr 0 3 4 (by decide) (by decide) with h11632 | h11632
      · rcases m.htr 0 3 5 (by decide) (by decide) with h11633 | h11633
        · rcases m.htr 0 4 5 (by decide) (by decide) with h11634 | h11634
          · rcases m.htr 1 2 3 (by decide) (by decide) with h11635 | h11635
            · linarith only [h0, h10008, h10009, h11635, hc12, hlam, hphi, ht01, u0ehi4]
            · linarith only [h0, h10008, h11635, hc23, hlam, hphi, ht01, ht12, u0ehi4]
          · linarith only [h0, h10008, h11617, h11634, hlam]
        · linarith only [h0, h10008, h11617, h11632, h11633, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h11640 | h11640
        · rcases m.htr 0 4 5 (by decide) (by decide) with h11641 | h11641
          · rcases m.htr 1 2 3 (by decide) (by decide) with h11642 | h11642
            · linarith only [h0, h10008, h10009, h11642, hc12, hlam, hphi, ht01, u0ehi4]
            · linarith only [h0, h10008, h11642, hc23, hlam, hphi, ht01, ht12, u0ehi4]
          · linarith only [h10008, h11632, h11641, h8410, hlam]
        · linarith only [h0, h10008, h10009, h11640, hlam]
    · linarith only [h0, h10008, h11631, hlam]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h10009 | h10009
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009

end R2N4
