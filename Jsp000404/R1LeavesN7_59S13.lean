import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_59S11
import Jsp000404.R1LeavesN7_59S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3548000 in
set_option maxHeartbeats 3548000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_R_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h843 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1185 | h1185
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1186 | h1186
    · linarith only [h1186, h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1188 | h1188
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1189 | h1189
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1190 | h1190
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1191 | h1191
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1192 | h1192
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1193 | h1193
                · linarith only [h1185, h1193, h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1195 | h1195
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1196 | h1196
                    · linarith only [h1185, h1193, h1196, h843, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1198 | h1198
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1199 | h1199
                        · linarith only [h1186, h1196, h1199, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases h0bigk with h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c | h1201c
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [hlam, p1201_0]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h0, hlam, p1201_1]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h843, hlam, p1201_0]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h843, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1201_1, u3elo1]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1186, hlam, p1201_1]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1185, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p1201_1]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [hlam, p1201_0]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h0, h1192, hc12, hlam, hphi, ht01, ht0b, ht5b, p1201_1, u5ehi3]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            rcases p1201_3 (m.d 0 1) (by simp) with h1210 | h1210
                            · linarith only [h0, h1210, hlam]
                            · linarith only [h1185, h1210, hlam]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1201_1, u5ehi0]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1185, h1195, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1201_1]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1188, hlam, p1201_1]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [hlam, p1201_0]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1185, h1195, h843, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1201_1, u3elo1]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1185, h1186, h1195, h843, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1201_1, u3elo1]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1185, hlam, p1201_0]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1189, hlam, p1201_0]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1191, hlam, p1201_0]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [hlam, p1201_0]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1193, hlam, p1201_0]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1185, h1195, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1201_1]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1190, hlam, p1201_1]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1192, hlam, p1201_0]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [h1185, h1186, h1195, h1196, hc34, hc45, hlam, hphi, p1201_1]
                          · have p1201_0 := h1201c.1
                            have p1201_1 := h1201c.2.1
                            have p1201_2 := h1201c.2.2.1
                            have p1201_3 := h1201c.2.2.2
                            linarith only [hlam, p1201_0]
                      · linarith only [h1185, h1195, h1198, h843, hc23, hlam, hphi, u3elo1]
                  · linarith only [h1195, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1231 | h1231
                · linarith only [h1185, h1231, h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1233 | h1233
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1234 | h1234
                    · linarith only [h1185, h1192, h1231, h1234, h843, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1236 | h1236
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1237 | h1237
                        · linarith only [h1234, h1236, h1237, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi1]
                        · rcases h0bigk with h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c | h1239c
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h0, hlam, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h843, hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1192, h843, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1239_1, u3elo4]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1186, hlam, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h0, h1185, h1233, h843, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            rcases p1239_3 (m.d 0 1) (by simp) with h1248 | h1248
                            · linarith only [h0, h1248, hlam]
                            · linarith only [h1185, h1248, hlam]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h0, h1185, h1192, h1233, h843, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1185, h1233, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1188, hlam, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1185, h1233, h843, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1239_1, u3elo1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1192, hlam, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1185, hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1189, hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1191, hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1231, hlam, p1239_0]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h0, h1185, h1190, h1233, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1190, hlam, p1239_1]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1192, hc03, hlam, hphi, p1239_1, u3elo4]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [h1185, h1192, h1233, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1239_1, u3elo4]
                          · have p1239_0 := h1239c.1
                            have p1239_1 := h1239c.2.1
                            have p1239_2 := h1239c.2.2.1
                            have p1239_3 := h1239c.2.2.2
                            linarith only [hlam, p1239_0]
                      · linarith only [h1185, h1233, h1236, h843, hc23, hlam, hphi, u3elo0]
                  · linarith only [h1185, h1233, h843, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
            · linarith only [h1185, h1191, h843, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1270 | h1270
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1271 | h1271
              · linarith only [h1188, h1190, h1271, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1273 | h1273
                · linarith only [h1185, h1273, h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1275 | h1275
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1276 | h1276
                    · linarith only [h1185, h1190, h1271, h1273, h1276, h843, hc02, hlam, hphi, ht23, u3elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1278 | h1278
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1279 | h1279
                        · linarith only [h1188, h1276, h1278, h1279, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases h0bigk with h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [hlam, p1281_0]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h0, hlam, p1281_1]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h843, hlam, p1281_0]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1271, h843, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1281_1, u3elo4]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1186, hlam, p1281_1]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1190, h1271, hc01, hlam, hphi, ht12, ht23, p1281_1, u3elo4]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [hlam, p1281_0]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1190, h1271, hc03, hlam, hphi, p1281_1, u3elo4]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1185, h1190, h1271, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1281_1, u3elo4]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1190, hlam, p1281_0]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1185, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p1281_1]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1188, hlam, p1281_1]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [hlam, p1281_0]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1188, h1190, h1271, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1281_1, u3elo4]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1271, hlam, p1281_1]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1185, hlam, p1281_0]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1189, hlam, p1281_0]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1270, hlam, p1281_0]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [hlam, p1281_0]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1273, hlam, p1281_0]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1185, h1271, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1281_1, u3elo4]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1271, hc02, hlam, hphi, ht23, p1281_1, u3elo4]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1271, hc03, hlam, hphi, p1281_1, u3elo4]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [h1189, h1271, h1278, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1281_1, u3elo4]
                          · have p1281_0 := h1281c.1
                            have p1281_1 := h1281c.2.1
                            have p1281_2 := h1281c.2.2.1
                            have p1281_3 := h1281c.2.2.2
                            linarith only [hlam, p1281_0]
                      · linarith only [h1185, h1275, h1278, h843, hc23, hlam, hphi, u3elo0]
                  · linarith only [h1275, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h1185, h1270, h843, hlam]
        · linarith only [h0, h1185, h1189, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1311 | h1311
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1312 | h1312
          · linarith only [h1188, h1312, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1314 | h1314
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1315 | h1315
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1316 | h1316
                · linarith only [h0, h1185, h1188, h1316, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1318 | h1318
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1319 | h1319
                    · linarith only [h0, h1185, h1188, h1316, h1319, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1321 | h1321
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1322 | h1322
                        · linarith only [h1186, h1319, h1322, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases h0bigk with h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h0, hlam, p1324_1]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h843, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h0, h1188, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1324_1, u3elo2]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1186, hlam, p1324_1]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1188, hc01, hlam, hphi, ht12, ht23, p1324_1, u3elo2]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1188, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1185, h1188, h1318, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1324_1, u3elo2]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1312, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1185, h1318, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1324_1]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h843, hc02, hlam, hphi, ht23, p1324_1, u3elo1]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1185, h1318, h843, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1324_1, u3elo1]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1324_1, u3elo1, u5ehi0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1185, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1311, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1314, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1316, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1185, h1318, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1324_1]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h0, h1185, h1318, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1324_1]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1315, hlam, p1324_0]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [h1185, h1315, h1318, h843, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1324_1, u3elo1]
                          · have p1324_0 := h1324c.1
                            have p1324_1 := h1324c.2.1
                            have p1324_2 := h1324c.2.2.1
                            have p1324_3 := h1324c.2.2.2
                            linarith only [hlam, p1324_0]
                      · linarith only [h1185, h1318, h1321, h843, hc23, hlam, hphi, u3elo1]
                  · linarith only [h1185, h1318, h843, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1352 | h1352
                · linarith only [h1185, h1352, h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1354 | h1354
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1355 | h1355
                    · linarith only [h0, h1185, h1188, h1315, h1352, h1355, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1357 | h1357
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1358 | h1358
                        · linarith only [h1186, h1355, h1358, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases h0bigk with h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h0, hlam, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h843, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h0, h1185, h1188, h1315, h1354, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1360_1, u3elo4]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1186, hlam, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1188, h1315, hc01, hlam, hphi, ht12, ht23, p1360_1, u3elo4]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1188, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1185, h1188, h1315, h1354, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1360_1, u3elo4]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1312, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1185, h1315, h1354, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1360_1, u3elo4]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1315, hc02, hlam, hphi, ht23, p1360_1, u3elo4]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1185, h1315, h1354, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1360_1, u3elo4]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1315, hlam, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1185, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1311, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1314, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1352, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1185, h1354, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h0, h1185, h1186, h1354, h1355, hc34, hc45, hlam, hphi, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1315, hc03, hlam, hphi, p1360_1, u3elo4]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1185, h1315, h1354, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1360_1, u3elo4]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [hlam, p1360_0]
                      · linarith only [h0, h1185, h1188, h1354, h1357, hc23, hlam, hphi, u3elo0]
                  · linarith only [h1185, h1354, h843, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
            · linarith only [h0, h1185, h1188, h1314, hlam]
        · linarith only [h0, h1185, h1311, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1390 | h1390
    · linarith only [h1390, h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1392 | h1392
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1393 | h1393
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1394 | h1394
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1395 | h1395
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1396 | h1396
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1397 | h1397
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1398 | h1398
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1399 | h1399
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1400 | h1400
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1401 | h1401
                        · linarith only [h1392, h1400, h1401, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases h0bigk with h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [hlam, p1403_0]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h0, hlam, p1403_1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h843, hlam, p1403_0]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1185, hlam, p1403_1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1390, hlam, p1403_1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1403_1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [hlam, p1403_0]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h0, h843, hc01, hc12, hlam, hphi, p1403_1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h0, h1397, h1401, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1403_1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1403_1, u5ehi0]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, p1403_1, u3elo0]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1392, hlam, p1403_1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [hlam, p1403_0]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1397, h1401, h843, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1403_1, u3elo1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1394, h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1403_1, u3elo1, u5ehi2]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1185, h1398, hc01, hlam, hphi, ht12, ht23, p1403_1, u3elo1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1393, hlam, p1403_0]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1395, hlam, p1403_0]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [hlam, p1403_0]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1185, h1394, h1398, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1403_1, u3elo1, u5ehi2]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1390, h1398, h1399, hc01, hlam, hphi, ht12, ht23, p1403_1, u3elo1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1394, hlam, p1403_1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1396, hlam, p1403_0]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [h1397, hlam, p1403_1]
                          · have p1403_0 := h1403c.1
                            have p1403_1 := h1403c.2.1
                            have p1403_2 := h1403c.2.2.1
                            have p1403_3 := h1403c.2.2.2
                            linarith only [hlam, p1403_0]
                      · linarith only [h1395, h1400, h843, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1185, h1397, h1399, hlam]
                  · linarith only [h1395, h1398, h843, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1432 | h1432
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1433 | h1433
                    · linarith only [h1185, h1397, h1432, h1433, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1435 | h1435
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1436 | h1436
                        · linarith only [h1433, h1435, h1436, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · rcases h0bigk with h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [hlam, p1438_0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h0, hlam, p1438_1]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h843, hlam, p1438_0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1185, hlam, p1438_1]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1390, hlam, p1438_1]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1438_1]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [hlam, p1438_0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h0, h1396, hc12, hlam, hphi, ht01, ht0b, ht5b, p1438_1, u5ehi0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h0, h1185, hc01, hc12, hlam, hphi, p1438_1]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1438_1, u5ehi0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, p1438_1, u3elo0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1392, hlam, p1438_1]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [hlam, p1438_0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1185, h843, hc01, hlam, hphi, ht12, ht23, p1438_1, u3elo1]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1394, h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1438_1, u3elo1, u5ehi2]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1185, hc01, hc14, hlam, hphi, p1438_1]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1393, hlam, p1438_0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1395, hlam, p1438_0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [hlam, p1438_0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1397, hlam, p1438_0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1390, hc01, hc15, hlam, hphi, p1438_1]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1394, hlam, p1438_1]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1396, hlam, p1438_0]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [h1396, h843, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1438_1, u3elo1]
                          · have p1438_0 := h1438c.1
                            have p1438_1 := h1438c.2.1
                            have p1438_2 := h1438c.2.2.1
                            have p1438_3 := h1438c.2.2.2
                            linarith only [hlam, p1438_0]
                      · linarith only [h1395, h1435, h843, hc23, hlam, hphi, u3elo1]
                  · linarith only [h1432, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1466 | h1466
                · linarith only [h1395, h1396, h1466, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1468 | h1468
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1469 | h1469
                    · linarith only [h1185, h1466, h1468, h1469, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1471 | h1471
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1472 | h1472
                        · linarith only [h1392, h1396, h1469, h1471, h1472, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · rcases h0bigk with h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c | h1474c
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [hlam, p1474_0]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h0, hlam, p1474_1]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h843, hlam, p1474_0]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1185, hlam, p1474_1]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1390, hlam, p1474_1]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1474_1]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [hlam, p1474_0]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h0, h1392, h1471, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1474_1]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h0, h1185, hc01, hc12, hlam, hphi, p1474_1]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1474_1, u5ehi0]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1396, hc01, hlam, hphi, ht12, ht23, p1474_1, u3elo4]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1392, hlam, p1474_1]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [hlam, p1474_0]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1185, h1396, hc01, hlam, hphi, ht12, ht23, p1474_1, u3elo4]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1396, hlam, p1474_1]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1185, hc01, hc14, hlam, hphi, p1474_1]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1393, hlam, p1474_0]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1395, hlam, p1474_0]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [hlam, p1474_0]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1466, hlam, p1474_0]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1390, hc01, hc15, hlam, hphi, p1474_1]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1394, hlam, p1474_1]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1396, hc03, hlam, hphi, p1474_1, u3elo4]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [h1185, h1396, hc01, hlam, hphi, ht12, ht23, p1474_1, u3elo4]
                          · have p1474_0 := h1474c.1
                            have p1474_1 := h1474c.2.1
                            have p1474_2 := h1474c.2.2.1
                            have p1474_3 := h1474c.2.2.2
                            linarith only [hlam, p1474_0]
                      · linarith only [h1395, h1471, hc23, hlam, hphi, u3elo0]
                  · linarith only [h1395, h1396, h1468, hc13, hlam, hphi, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1502 | h1502
              · linarith only [h1395, h1502, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1504 | h1504
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1505 | h1505
                  · linarith only [h1395, h1505, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1505, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1508 | h1508
                  · linarith only [h1395, h1508, h843, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1508, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1511 | h1511
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1512 | h1512
              · linarith only [h1392, h1394, h1512, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1514 | h1514
                · linarith only [h1511, h1512, h1514, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1516 | h1516
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1517 | h1517
                    · linarith only [h1185, h1514, h1516, h1517, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1519 | h1519
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1520 | h1520
                        · linarith only [h1392, h1517, h1519, h1520, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c | h1522c
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [hlam, p1522_0]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h0, hlam, p1522_1]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h843, hlam, p1522_0]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1185, hlam, p1522_1]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1390, hlam, p1522_1]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1394, h1512, hc01, hlam, hphi, ht12, ht23, p1522_1, u3elo4]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [hlam, p1522_0]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1394, h1512, hc03, hlam, hphi, p1522_1, u3elo4]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1185, h1394, h1512, hc01, hlam, hphi, ht12, ht23, p1522_1, u3elo4]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1394, hlam, p1522_0]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, p1522_1, u3elo0]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1392, hlam, p1522_1]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [hlam, p1522_0]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1185, h1392, h1394, h1512, hc01, hlam, hphi, ht12, ht23, p1522_1, u3elo4]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1512, hlam, p1522_1]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1185, hc01, hc14, hlam, hphi, p1522_1]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1393, hlam, p1522_0]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1511, hlam, p1522_0]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [hlam, p1522_0]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1514, hlam, p1522_0]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1512, hc01, hlam, hphi, ht12, ht23, p1522_1, u3elo4]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1392, h1512, h1519, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1522_1, u3elo4]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1512, hc03, hlam, hphi, p1522_1, u3elo4]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [h1185, h1512, hc01, hlam, hphi, ht12, ht23, p1522_1, u3elo4]
                          · have p1522_0 := h1522c.1
                            have p1522_1 := h1522c.2.1
                            have p1522_2 := h1522c.2.2.1
                            have p1522_3 := h1522c.2.2.2
                            linarith only [hlam, p1522_0]
                      · linarith only [h1511, h1519, hc23, hlam, hphi, u3elo0]
                  · linarith only [h1511, h1512, h1516, hc13, hlam, hphi, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1550 | h1550
              · linarith only [h1511, h1550, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1552 | h1552
                · linarith only [h1393, h1394, h1552, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1554 | h1554
                  · linarith only [h1511, h1554, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1554, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1557 | h1557
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1558 | h1558
            · linarith only [h1392, h1393, h1558, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1560 | h1560
              · linarith only [h1558, h1560, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1562 | h1562
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1563 | h1563
                  · linarith only [h1558, h1563, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1563, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1393, h1557, h1562, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1567 | h1567
            · linarith only [h1392, h1393, h1567, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1569 | h1569
              · linarith only [h1567, h1569, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1571 | h1571
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1572 | h1572
                  · linarith only [h1567, h1572, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1572, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1575 | h1575
                  · linarith only [h1567, h1575, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1575, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1578 | h1578
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1579 | h1579
          · linarith only [h1392, h1579, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1581 | h1581
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1582 | h1582
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1583 | h1583
                · linarith only [h1392, h1578, h1583, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1585 | h1585
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1586 | h1586
                    · linarith only [h1185, h1583, h1585, h1586, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1588 | h1588
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1589 | h1589
                        · linarith only [h1392, h1578, h1586, h1588, h1589, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · rcases h0bigk with h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c | h1591c
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [hlam, p1591_0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h0, hlam, p1591_1]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h843, hlam, p1591_0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1185, hlam, p1591_1]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1390, hlam, p1591_1]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1392, hc01, hlam, hphi, ht12, ht23, p1591_1, u3elo2]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [hlam, p1591_0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1392, hlam, p1591_0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1185, h1392, hc01, hlam, hphi, ht12, ht23, p1591_1, u3elo2]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1579, hlam, p1591_0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h843, hc01, hlam, hphi, ht12, ht23, p1591_1, u3elo1]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h843, hc02, hlam, hphi, ht23, p1591_1, u3elo1]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [hlam, p1591_0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1185, h843, hc01, hlam, hphi, ht12, ht23, p1591_1, u3elo1]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1591_1, u3elo1, u5ehi0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1185, hc01, hc14, hlam, hphi, p1591_1]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1578, hlam, p1591_0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1581, hlam, p1591_0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [hlam, p1591_0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1583, hlam, p1591_0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1390, hc01, hc15, hlam, hphi, p1591_1]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1578, h1579, h1588, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1591_1]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1582, hlam, p1591_0]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [h1582, h843, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1591_1, u3elo1]
                          · have p1591_0 := h1591c.1
                            have p1591_1 := h1591c.2.1
                            have p1591_2 := h1591c.2.2.1
                            have p1591_3 := h1591c.2.2.2
                            linarith only [hlam, p1591_0]
                      · linarith only [h1392, h1588, hc02, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1582, h1585, h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1619 | h1619
                · linarith only [h1392, h1578, h1619, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1621 | h1621
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1622 | h1622
                    · linarith only [h1185, h1619, h1621, h1622, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1624 | h1624
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1625 | h1625
                        · linarith only [h1392, h1578, h1582, h1622, h1624, h1625, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · rcases h0bigk with h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [hlam, p1627_0]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h0, hlam, p1627_1]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h843, hlam, p1627_0]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1185, hlam, p1627_1]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1390, hlam, p1627_1]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1392, h1582, hc01, hlam, hphi, ht12, ht23, p1627_1, u3elo4]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [hlam, p1627_0]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1392, hlam, p1627_0]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1185, h1392, h1582, hc01, hlam, hphi, ht12, ht23, p1627_1, u3elo4]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1579, hlam, p1627_0]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1582, hc01, hlam, hphi, ht12, ht23, p1627_1, u3elo4]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1582, hc02, hlam, hphi, ht23, p1627_1, u3elo4]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [hlam, p1627_0]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1185, h1582, hc01, hlam, hphi, ht12, ht23, p1627_1, u3elo4]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1582, hlam, p1627_1]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1185, hc01, hc14, hlam, hphi, p1627_1]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1578, hlam, p1627_0]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1581, hlam, p1627_0]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [hlam, p1627_0]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1619, hlam, p1627_0]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1390, hc01, hc15, hlam, hphi, p1627_1]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1579, hc02, hc25, hlam, hphi, p1627_1]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1582, hc03, hlam, hphi, p1627_1, u3elo4]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [h1185, h1582, hc01, hlam, hphi, ht12, ht23, p1627_1, u3elo4]
                          · have p1627_0 := h1627c.1
                            have p1627_1 := h1627c.2.1
                            have p1627_2 := h1627c.2.2.1
                            have p1627_3 := h1627c.2.2.2
                            linarith only [hlam, p1627_0]
                      · linarith only [h1392, h1624, hc02, hlam, hphi, ht23, u3elo3]
                  · linarith only [h1581, h1582, h1621, hc13, hlam, hphi, u3elo4]
            · linarith only [h1392, h1578, h1581, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1656 | h1656
          · linarith only [h1392, h1656, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1658 | h1658
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1659 | h1659
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1660 | h1660
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1661 | h1661
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1662 | h1662
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1663 | h1663
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1664 | h1664
                        · linarith only [h1658, h1664, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                        · rcases h0bigk with h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c | h1666c
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [hlam, p1666_0]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h0, hlam, p1666_1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h843, hlam, p1666_0]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1185, hlam, p1666_1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1390, hlam, p1666_1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1578, h1663, hc01, hlam, hphi, ht12, ht23, p1666_1, u3elo2]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [hlam, p1666_0]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1392, hlam, p1666_0]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1578, hlam, p1666_1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1656, hlam, p1666_0]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h843, hc01, hlam, hphi, ht12, ht23, p1666_1, u3elo1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h843, hc02, hlam, hphi, ht23, p1666_1, u3elo1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [hlam, p1666_0]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1660, h1664, h843, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1666_1, u3elo1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1666_1, u3elo1, u5ehi0]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1185, h1661, hc01, hlam, hphi, ht12, ht23, p1666_1, u3elo1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h0, h1185, h1661, hc01, hlam, hphi, ht12, ht23, p1666_1, u3elo1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1658, hlam, p1666_0]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [hlam, p1666_0]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1185, h1659, h1661, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1666_1, u3elo1, u5ehi3]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1390, h1661, h1662, hc01, hlam, hphi, ht12, ht23, p1666_1, u3elo1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h0, h1390, h1661, h1662, hc01, hlam, hphi, ht12, ht23, p1666_1, u3elo1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1659, hlam, p1666_0]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [h1660, hlam, p1666_1]
                          · have p1666_0 := h1666c.1
                            have p1666_1 := h1666c.2.1
                            have p1666_2 := h1666c.2.2.1
                            have p1666_3 := h1666c.2.2.2
                            linarith only [hlam, p1666_0]
                      · linarith only [h0, h1392, h1663, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h1185, h1660, h1662, hlam]
                  · linarith only [h1658, h1661, h843, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1695 | h1695
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1696 | h1696
                    · linarith only [h1185, h1660, h1695, h1696, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1698 | h1698
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1699 | h1699
                        · linarith only [h1185, h1696, h1699, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases h0bigk with h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c | h1701c
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [hlam, p1701_0]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h0, hlam, p1701_1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h843, hlam, p1701_0]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h1185, hlam, p1701_1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h1390, hlam, p1701_1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h0, hc01, hc12, hlam, hphi, p1701_1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [hlam, p1701_0]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h1392, hlam, p1701_0]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h1578, hlam, p1701_1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h1656, hlam, p1701_0]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h843, hc01, hlam, hphi, ht12, ht23, p1701_1, u3elo1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h843, hc02, hlam, hphi, ht23, p1701_1, u3elo1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [hlam, p1701_0]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h843, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1701_1, u3elo1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h843, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1701_1, u3elo1, u5ehi0]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h1185, hc01, hc14, hlam, hphi, p1701_1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h0, h1185, h1696, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1701_1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h1658, hlam, p1701_0]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [hlam, p1701_0]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h1660, hlam, p1701_0]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h1656, hc01, hc25, hlam, hphi, ht12, p1701_1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h0, h1656, hc01, hc25, hlam, hphi, ht12, p1701_1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h1659, hlam, p1701_0]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [h1659, h843, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1701_1, u3elo1]
                          · have p1701_0 := h1701c.1
                            have p1701_1 := h1701c.2.1
                            have p1701_2 := h1701c.2.2.1
                            have p1701_3 := h1701c.2.2.2
                            linarith only [hlam, p1701_0]
                      · linarith only [h0, h1392, h1698, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h1658, h1695, h843, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1729 | h1729
                · linarith only [h1658, h1659, h1729, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1731 | h1731
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1732 | h1732
                    · linarith only [h1185, h1729, h1731, h1732, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1734 | h1734
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1735 | h1735
                        · linarith only [h1658, h1659, h1732, h1735, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · rcases h0bigk with h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c | h1737c
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [hlam, p1737_0]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h0, hlam, p1737_1]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h843, hlam, p1737_0]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1185, hlam, p1737_1]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1390, hlam, p1737_1]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1578, h1734, hc01, hc23, hlam, hphi, ht12, p1737_1]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [hlam, p1737_0]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1392, hlam, p1737_0]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1578, hlam, p1737_1]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1656, hlam, p1737_0]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1659, hc01, hlam, hphi, ht12, ht23, p1737_1, u3elo4]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1659, hc02, hlam, hphi, ht23, p1737_1, u3elo4]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [hlam, p1737_0]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h0, h1578, h1659, hc01, hlam, hphi, ht12, ht23, p1737_1, u3elo4]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1659, hlam, p1737_1]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1185, hc01, hc14, hlam, hphi, p1737_1]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h0, h1185, h1732, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1737_1]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1658, hlam, p1737_0]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [hlam, p1737_0]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1729, hlam, p1737_0]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1390, hc01, hc15, hlam, hphi, p1737_1]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h0, h1656, hc01, hc25, hlam, hphi, ht12, p1737_1]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1659, hc03, hlam, hphi, p1737_1, u3elo4]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [h1659, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1737_1, u3elo4]
                          · have p1737_0 := h1737c.1
                            have p1737_1 := h1737c.2.1
                            have p1737_2 := h1737c.2.2.1
                            have p1737_3 := h1737c.2.2.2
                            linarith only [hlam, p1737_0]
                      · linarith only [h1658, h1734, hc23, hlam, hphi, u3elo0]
                  · linarith only [h1658, h1731, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1765 | h1765
              · linarith only [h1658, h1765, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1767 | h1767
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1768 | h1768
                  · linarith only [h1658, h1768, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1768, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1771 | h1771
                  · linarith only [h0, h1392, h1658, h1771, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1771, h843, hc01, hlam, hphi, ht12, ht23, u3elo3]

set_option maxHeartbeats 3548000 in
set_option maxHeartbeats 3548000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h843 | h843
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_R_x1_x0 m hb0 hb2 hb3 hb5 h0 h843
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_R_x1_x1 m hb0 hb2 hb3 hb5 h0 h843

set_option maxHeartbeats 3548000 in
set_option maxHeartbeats 3548000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_R_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_H_I_L_I_L_0_L_R_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
