import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_53S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h856 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h857 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h1241 | h1241
  · linarith only [h1241, h857, hc34, hlam, hphi, u3ehi4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1243 | h1243
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1244 | h1244
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1245 | h1245
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1246 | h1246
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1247 | h1247
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1248 | h1248
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1249 | h1249
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1250 | h1250
                  · linarith only [h1250, h855, h857, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1252 | h1252
                    · linarith only [h1241, h1252, h855, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1254 | h1254
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1255 | h1255
                        · rcases h0emax with h1256 | h1256 | h1256 | h1256 | h1256
                          · rcases h5bigk with h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [hlam, p1257_0]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h674, hlam, p1257_1]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1252, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1257_1, u2ehi2]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1241, hlam, p1257_1]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1241, h1244, h1247, h1255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1257_1]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1244, h1247, h1249, h674, hc01, hc12, hlam, hphi, p1257_1]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [hlam, p1257_0]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1244, h1247, h1249, h1252, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1257_1, u2ehi2]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1241, h1244, h1247, h1249, h855, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1257_1, u2ehi2]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              rcases p1257_3 (m.d 0 5) (by simp) with h1267 | h1267
                              · linarith only [h1267, h674, hlam]
                              · linarith only [h1243, h1267, hlam]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h856, hlam, p1257_1]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1246, hlam, p1257_1]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [hlam, p1257_0]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1252, hlam, p1257_1]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h856, hc02, hc45, hlam, hphi, ht0b, ht5b, p1257_1]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1255, h856, hc34, hlam, hphi, ht23, p1257_1, u2ehi4]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1248, hlam, p1257_0]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1244, h1247, h1255, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1257_1, u2ehi4]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [hlam, p1257_0]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1244, h1247, h1255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1257_1]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1243, hlam, p1257_0]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1249, hlam, p1257_0]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1254, hlam, p1257_0]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [h1255, hlam, p1257_0]
                            · have p1257_0 := h1257c.1
                              have p1257_1 := h1257c.2.1
                              have p1257_2 := h1257c.2.2.1
                              have p1257_3 := h1257c.2.2.2
                              linarith only [hlam, p1257_0]
                          · linarith only [h1256, h855, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases h5bigk with h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [hlam, p1286_0]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h674, hlam, p1286_1]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1252, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1286_1, u2ehi2]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1241, hlam, p1286_1]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1241, h1244, h1247, h1255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1286_1]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1244, h1247, h1249, h674, hc01, hc12, hlam, hphi, p1286_1]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [hlam, p1286_0]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1244, h1247, h1249, h1252, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1286_1, u2ehi2]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1241, h1244, h1247, h1249, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1286_1, u3ehi0]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              rcases p1286_3 (m.d 0 5) (by simp) with h1296 | h1296
                              · linarith only [h1296, h674, hlam]
                              · linarith only [h1243, h1296, hlam]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h856, hlam, p1286_1]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1246, hlam, p1286_1]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [hlam, p1286_0]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1252, hlam, p1286_1]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h856, hc02, hc45, hlam, hphi, ht0b, ht5b, p1286_1]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h856, hc35, hlam, hphi, ht23, p1286_1, u2ehi4]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1248, hlam, p1286_0]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1244, h1248, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1286_1, u2ehi4]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [hlam, p1286_0]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1244, h1247, h1255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1286_1]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1243, hlam, p1286_0]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1249, hlam, p1286_0]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1254, hlam, p1286_0]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [h1255, hlam, p1286_0]
                            · have p1286_0 := h1286c.1
                              have p1286_1 := h1286c.2.1
                              have p1286_2 := h1286c.2.2.1
                              have p1286_3 := h1286c.2.2.2
                              linarith only [hlam, p1286_0]
                          · rcases h5bigk with h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [hlam, p1314_0]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h674, hlam, p1314_1]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1252, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1314_1, u2ehi2]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1241, hlam, p1314_1]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1243, h1256, hc45, hlam, hphi, ht0b, ht5b, p1314_1]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1244, h1247, h1249, h674, hc01, hc12, hlam, hphi, p1314_1]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [hlam, p1314_0]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1244, h1247, h1249, h1252, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1314_1, u2ehi2]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1244, h1247, h1249, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1314_1, u3ehi4]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              rcases p1314_3 (m.d 0 5) (by simp) with h1324 | h1324
                              · linarith only [h1324, h674, hlam]
                              · linarith only [h1243, h1324, hlam]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h856, hlam, p1314_1]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1246, hlam, p1314_1]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [hlam, p1314_0]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1252, hlam, p1314_1]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h0, h856, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1314_1]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h856, hc35, hlam, hphi, ht23, p1314_1, u2ehi4]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1248, hlam, p1314_0]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1244, h1248, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1314_1, u2ehi4]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [hlam, p1314_0]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1244, h1247, h1255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1314_1]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1243, hlam, p1314_0]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1249, hlam, p1314_0]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1254, hlam, p1314_0]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [h1255, hlam, p1314_0]
                            · have p1314_0 := h1314c.1
                              have p1314_1 := h1314c.2.1
                              have p1314_2 := h1314c.2.2.1
                              have p1314_3 := h1314c.2.2.2
                              linarith only [hlam, p1314_0]
                          · rcases h5bigk with h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c | h1342c
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [hlam, p1342_0]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h674, hlam, p1342_1]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1252, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1342_1, u2ehi2]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1241, hlam, p1342_1]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1241, h1244, h1247, h1255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1342_1]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1244, h1247, h1249, h674, hc01, hc12, hlam, hphi, p1342_1]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [hlam, p1342_0]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1244, h1247, h1249, h1252, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1342_1, u2ehi2]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1244, h1247, h1249, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1342_1, u3ehi4]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              rcases p1342_3 (m.d 0 5) (by simp) with h1352 | h1352
                              · linarith only [h1352, h674, hlam]
                              · linarith only [h1243, h1352, hlam]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h856, hlam, p1342_1]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1246, hlam, p1342_1]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [hlam, p1342_0]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1252, hlam, p1342_1]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h0, h856, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1342_1]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h856, hc35, hlam, hphi, ht23, p1342_1, u2ehi4]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1248, hlam, p1342_0]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1244, h1248, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1342_1, u2ehi4]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [hlam, p1342_0]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1244, h1247, h1255, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1342_1]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1243, hlam, p1342_0]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1249, hlam, p1342_0]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1254, hlam, p1342_0]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [h1255, hlam, p1342_0]
                            · have p1342_0 := h1342c.1
                              have p1342_1 := h1342c.2.1
                              have p1342_2 := h1342c.2.2.1
                              have p1342_3 := h1342c.2.2.2
                              linarith only [hlam, p1342_0]
                        · linarith only [h1255, h855, h857, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h1243, h1254, h857, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h1243, h1244, h1245, h1247, h1249, h857, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h1247, h1248, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1374 | h1374
              · linarith only [h1247, h1374, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1376 | h1376
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1377 | h1377
                  · linarith only [h1247, h1377, h855, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1379 | h1379
                    · linarith only [h1374, h1379, h482, h855, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1381 | h1381
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1382 | h1382
                        · rcases h0emax with h1383 | h1383 | h1383 | h1383 | h1383
                          · rcases h5bigk with h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c | h1384c
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h674, hlam, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h674, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1384_1, u2ehi4]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1241, hlam, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              rcases p1384_3 (m.d 0 5) (by simp) with h1389 | h1389
                              · rcases p1384_3 (m.d 1 5) (by simp) with h1390 | h1390
                                · rcases p1384_3 (m.d 2 5) (by simp) with h1391 | h1391
                                  · linarith only [h1391, h856, hlam]
                                  · linarith only [h1381, h1391, hlam]
                                · linarith only [h1376, h1390, hlam]
                              · linarith only [h1243, h1389, hlam]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1247, h1376, h674, hc01, hc34, hlam, hphi, ht12, ht23, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1247, h1376, h1379, hc34, hlam, hphi, ht23, p1384_1, u2ehi2]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1374, hlam, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              rcases p1384_3 (m.d 0 5) (by simp) with h1400 | h1400
                              · linarith only [h1400, h674, hlam]
                              · linarith only [h1243, h1400, hlam]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h856, hlam, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1246, hlam, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1379, hlam, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h0, h856, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h856, hc35, hlam, hphi, ht23, p1384_1, u2ehi4]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h674, hc01, hc35, hlam, hphi, ht12, ht23, p1384_1]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hc35, hlam, hphi, ht23, p1384_1, u2ehi4]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              rcases p1384_3 (m.d 0 5) (by simp) with h1412 | h1412
                              · linarith only [h1241, h1412, hlam]
                              · linarith only [h1243, h1412, hlam]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1243, hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1376, hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1381, hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [h1382, hlam, p1384_0]
                            · have p1384_0 := h1384c.1
                              have p1384_1 := h1384c.2.1
                              have p1384_2 := h1384c.2.2.1
                              have p1384_3 := h1384c.2.2.2
                              linarith only [hlam, p1384_0]
                          · linarith only [h1383, h855, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases h5bigk with h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c | h1421c
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [hlam, p1421_0]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h674, hlam, p1421_1]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1243, h1379, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1421_1, u2ehi2]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1241, hlam, p1421_1]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              rcases p1421_3 (m.d 0 5) (by simp) with h1426 | h1426
                              · rcases p1421_3 (m.d 1 5) (by simp) with h1427 | h1427
                                · rcases p1421_3 (m.d 2 5) (by simp) with h1428 | h1428
                                  · linarith only [h1428, h856, hlam]
                                  · linarith only [h1381, h1428, hlam]
                                · linarith only [h1376, h1427, hlam]
                              · linarith only [h1243, h1426, hlam]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1374, h1382, h674, hc01, hc34, hlam, hphi, ht12, ht23, p1421_1]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [hlam, p1421_0]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1374, h1379, h1382, hc34, hlam, hphi, ht23, p1421_1, u2ehi2]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1374, hlam, p1421_1]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              rcases p1421_3 (m.d 0 5) (by simp) with h1437 | h1437
                              · linarith only [h1437, h674, hlam]
                              · linarith only [h1243, h1437, hlam]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h856, hlam, p1421_1]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1246, hlam, p1421_1]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [hlam, p1421_0]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1379, hlam, p1421_1]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h0, h856, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1421_1]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1382, h856, hc34, hlam, hphi, ht23, p1421_1, u2ehi4]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1382, h674, hc01, hc34, hlam, hphi, ht12, ht23, p1421_1]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1382, hc34, hlam, hphi, ht23, p1421_1, u2ehi4]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [hlam, p1421_0]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              rcases p1421_3 (m.d 0 5) (by simp) with h1449 | h1449
                              · linarith only [h1241, h1449, hlam]
                              · linarith only [h1243, h1449, hlam]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1243, hlam, p1421_0]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1376, hlam, p1421_0]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1381, hlam, p1421_0]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [h1382, hlam, p1421_0]
                            · have p1421_0 := h1421c.1
                              have p1421_1 := h1421c.2.1
                              have p1421_2 := h1421c.2.2.1
                              have p1421_3 := h1421c.2.2.2
                              linarith only [hlam, p1421_0]
                          · rcases h5bigk with h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [hlam, p1457_0]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h674, hlam, p1457_1]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1243, h1379, h1383, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1457_1, u2ehi2]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1241, hlam, p1457_1]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1243, h1383, hc45, hlam, hphi, ht0b, ht5b, p1457_1]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h674, hc01, hc15, hlam, hphi, p1457_1]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [hlam, p1457_0]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1246, h1379, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1457_1, u2ehi2]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1374, hlam, p1457_1]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              rcases p1457_3 (m.d 0 5) (by simp) with h1467 | h1467
                              · linarith only [h1467, h674, hlam]
                              · linarith only [h1243, h1467, hlam]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h856, hlam, p1457_1]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1246, hlam, p1457_1]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [hlam, p1457_0]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1379, hlam, p1457_1]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h0, h856, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1457_1]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1382, h856, hc34, hlam, hphi, ht23, p1457_1, u2ehi4]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1241, h1382, h674, h855, hc34, hlam, hphi, ht23, p1457_1, u2ehi2]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1382, hc34, hlam, hphi, ht23, p1457_1, u2ehi4]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [hlam, p1457_0]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              rcases p1457_3 (m.d 0 5) (by simp) with h1479 | h1479
                              · linarith only [h1241, h1479, hlam]
                              · linarith only [h1243, h1479, hlam]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1243, hlam, p1457_0]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1376, hlam, p1457_0]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1381, hlam, p1457_0]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [h1382, hlam, p1457_0]
                            · have p1457_0 := h1457c.1
                              have p1457_1 := h1457c.2.1
                              have p1457_2 := h1457c.2.2.1
                              have p1457_3 := h1457c.2.2.2
                              linarith only [hlam, p1457_0]
                          · rcases h5bigk with h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [hlam, p1487_0]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h674, hlam, p1487_1]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1243, h1379, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1487_1, u2ehi2]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1241, hlam, p1487_1]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1383, hc45, hlam, hphi, ht0b, ht5b, p1487_1]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1374, h1382, h674, hc01, hc34, hlam, hphi, ht12, ht23, p1487_1]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [hlam, p1487_0]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1374, h1379, h1382, hc34, hlam, hphi, ht23, p1487_1, u2ehi2]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1374, hlam, p1487_1]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              rcases p1487_3 (m.d 0 5) (by simp) with h1497 | h1497
                              · linarith only [h1497, h674, hlam]
                              · linarith only [h1243, h1497, hlam]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h856, hlam, p1487_1]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1246, hlam, p1487_1]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [hlam, p1487_0]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1379, hlam, p1487_1]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1383, h856, hc45, hlam, hphi, ht0b, ht5b, p1487_1]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1379, h1382, h856, hc34, hlam, hphi, ht23, p1487_1, u2ehi2]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1382, h674, hc01, hc34, hlam, hphi, ht12, ht23, p1487_1]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1379, h1382, hc34, hlam, hphi, ht23, p1487_1, u2ehi2]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [hlam, p1487_0]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              rcases p1487_3 (m.d 0 5) (by simp) with h1509 | h1509
                              · linarith only [h1241, h1509, hlam]
                              · linarith only [h1243, h1509, hlam]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1243, hlam, p1487_0]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1376, hlam, p1487_0]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1381, hlam, p1487_0]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [h1382, hlam, p1487_0]
                            · have p1487_0 := h1487c.1
                              have p1487_1 := h1487c.2.1
                              have p1487_2 := h1487c.2.2.1
                              have p1487_3 := h1487c.2.2.2
                              linarith only [hlam, p1487_0]
                        · linarith only [h1382, h855, h857, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h1243, h1381, h857, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h1243, h1245, h1376, h857, hc34, hlam, hphi, ht23, u2ehi3]
          · linarith only [h0, h1246, h855, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h1245, h855, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h1244, h855, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1523 | h1523
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1524 | h1524
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1525 | h1525
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1526 | h1526
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1527 | h1527
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1528 | h1528
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1529 | h1529
                  · linarith only [h1529, h855, h857, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1531 | h1531
                    · linarith only [h1241, h1531, h855, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1533 | h1533
                      · linarith only [h1243, h1529, h1533, h855, h857, hc34, hlam, hphi, ht23, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1535 | h1535
                        · linarith only [h1243, h1523, h1526, h1535, h855, h857, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1535, h855, h857, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h1526, h1528, h855, h857, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h1526, h1527, h855, h857, hc35, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1540 | h1540
              · linarith only [h1526, h1540, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1542 | h1542
                · linarith only [h1243, h1526, h1542, h855, h857, hc34, hlam, hphi, ht23, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1544 | h1544
                  · linarith only [h1526, h1542, h1544, h482, h855, hc45, hlam, hphi, ht34, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1546 | h1546
                    · linarith only [h1526, h1542, h1546, h482, h855, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1548 | h1548
                      · linarith only [h1526, h1542, h1548, h482, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1550 | h1550
                        · linarith only [h1526, h1542, h1550, h482, h855, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h1550, h855, h857, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h0, h1525, h856, hlam]
        · linarith only [h0, h1524, h856, hc24, hlam, hphi, u2ehi4]
      · linarith only [h0, h1523, h855, h857, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h856 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h857 | h857
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h856 h857
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h856 h857

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h856 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  linarith only [h855, h856, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h856 | h856
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h856
  · exact r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 h0 h482 h674 h855 h856

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h855 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  linarith only [h1557, h855, hc23, hlam, hphi, u2ehi4]

end R2N4
