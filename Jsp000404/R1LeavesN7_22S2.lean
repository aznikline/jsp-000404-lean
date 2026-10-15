import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1220 | h1220
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1221 | h1221
    · linarith only [h1221, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1223 | h1223
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1224 | h1224
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1225 | h1225
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1226 | h1226
            · linarith only [h0, h1226, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1228 | h1228
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1229 | h1229
                · linarith only [h1, h1221, h1223, h1229, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1231 | h1231
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1232 | h1232
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1233 | h1233
                      · linarith only [h0, h1, h1221, h1225, h1231, h1233, hc02, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1235 | h1235
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1236 | h1236
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1237 | h1237
                            · rcases h0bigk with h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1235, h1237, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                rcases p1238_3 (m.d 0 1) (by simp) with h1241 | h1241
                                · rcases p1238_3 (m.d 0 2) (by simp) with h1242 | h1242
                                  · linarith only [h0, h1242, hlam]
                                  · linarith only [h1242, h4, hlam]
                                · linarith only [h1, h1241, hlam]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1225, h1226, h1235, h1237, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                rcases p1238_3 (m.d 0 1) (by simp) with h1247 | h1247
                                · rcases p1238_3 (m.d 0 2) (by simp) with h1248 | h1248
                                  · linarith only [h0, h1248, hlam]
                                  · linarith only [h1220, h1248, hlam]
                                · linarith only [h1247, h3, hlam]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h0, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1, h1225, h1233, h1235, h1237, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h5, hlam, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                rcases p1238_3 (m.d 0 1) (by simp) with h1256 | h1256
                                · rcases p1238_3 (m.d 0 2) (by simp) with h1257 | h1257
                                  · rcases p1238_3 (m.d 0 3) (by simp) with h1258 | h1258
                                    · linarith only [h1258, h4, hlam]
                                    · linarith only [h1223, h1258, hlam]
                                  · linarith only [h1220, h1257, hlam]
                                · linarith only [h1256, h3, hlam]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1, hlam, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h4, hlam, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1221, hlam, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                rcases p1238_3 (m.d 0 1) (by simp) with h1267 | h1267
                                · rcases p1238_3 (m.d 0 2) (by simp) with h1268 | h1268
                                  · rcases p1238_3 (m.d 0 3) (by simp) with h1269 | h1269
                                    · rcases p1238_3 (m.d 0 4) (by simp) with h1270 | h1270
                                      · rcases p1238_3 (m.d 0 5) (by simp) with h1271 | h1271
                                        · linarith only [h1223, h1271, hlam]
                                        · rcases h0emin with h1273 | h1273 | h1273 | h1273 | h1273
                                          · rcases h2bigk with h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1225, h1233, h1235, h1237, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1274_1]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1233, h1235, h1237, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1274_1]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h5, hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              rcases p1274_3 (m.d 0 2) (by simp) with h1279 | h1279
                                              · rcases p1274_3 (m.d 1 2) (by simp) with h1280 | h1280
                                                · linarith only [h0, h1280, hlam]
                                                · linarith only [h1228, h1280, hlam]
                                              · linarith only [h1279, hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h0, hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h0, h1235, h1237, hc01, hc45, hlam, hphi, ht0b, ht5b, p1274_1]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1226, hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              rcases p1274_3 (m.d 0 2) (by simp) with h1288 | h1288
                                              · rcases p1274_3 (m.d 1 2) (by simp) with h1289 | h1289
                                                · rcases p1274_3 (m.d 2 3) (by simp) with h1290 | h1290
                                                  · linarith only [h1225, h1290, hlam]
                                                  · linarith only [h1235, h1290, hlam]
                                                · linarith only [h1289, hlam, p1274_0]
                                              · linarith only [h1220, h1288, hlam]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h4, hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1225, hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1233, hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1233, h4, h5, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1274_1]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1233, h4, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1238_1, p1274_1]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1225, h1233, hc23, hc34, hlam, hphi, p1274_1]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              rcases p1274_3 (m.d 0 2) (by simp) with h1302 | h1302
                                              · linarith only [h1302, h5, hlam]
                                              · linarith only [h1302, h4, hlam]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1228, h3, h4, h5, hlam, p1238_1, p1274_2]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1220, hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1228, hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1235, hlam, p1274_1]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [h1236, hlam, p1274_0]
                                            · have p1274_0 := h1274c.1
                                              have p1274_1 := h1274c.2.1
                                              have p1274_2 := h1274c.2.2.1
                                              have p1274_3 := h1274c.2.2.2
                                              linarith only [hlam, p1274_0]
                                          · linarith only [h1273, h5, hc24, hlam, ht01, ht12]
                                          · linarith only [h1273, h4, h5, hc24, hlam, ht01, ht12]
                                          · rcases h2bigk with h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1225, h1233, h1235, h1237, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1314_1]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1233, h1235, h1237, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1314_1]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h5, hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              rcases p1314_3 (m.d 0 2) (by simp) with h1319 | h1319
                                              · rcases p1314_3 (m.d 1 2) (by simp) with h1320 | h1320
                                                · linarith only [h0, h1320, hlam]
                                                · linarith only [h1228, h1320, hlam]
                                              · linarith only [h1319, hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h0, hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h0, h1235, h1237, hc01, hc45, hlam, hphi, ht0b, ht5b, p1314_1]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1226, hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              rcases p1314_3 (m.d 0 2) (by simp) with h1328 | h1328
                                              · rcases p1314_3 (m.d 1 2) (by simp) with h1329 | h1329
                                                · rcases p1314_3 (m.d 2 3) (by simp) with h1330 | h1330
                                                  · linarith only [h1225, h1330, hlam]
                                                  · linarith only [h1235, h1330, hlam]
                                                · linarith only [h1329, hlam, p1314_0]
                                              · linarith only [h1220, h1328, hlam]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h4, hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1225, hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1233, hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1233, h1235, h1237, h4, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1314_1]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1233, h4, hc23, hc34, hlam, hphi, p1314_1]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1225, h1233, hc23, hc34, hlam, hphi, p1314_1]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              rcases p1314_3 (m.d 0 2) (by simp) with h1342 | h1342
                                              · linarith only [h1342, h5, hlam]
                                              · linarith only [h1342, h4, hlam]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1228, h3, h4, h5, hlam, p1238_1, p1314_2]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1220, hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1228, hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1235, hlam, p1314_1]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [h1236, hlam, p1314_0]
                                            · have p1314_0 := h1314c.1
                                              have p1314_1 := h1314c.2.1
                                              have p1314_2 := h1314c.2.2.1
                                              have p1314_3 := h1314c.2.2.2
                                              linarith only [hlam, p1314_0]
                                          · linarith only [h1273, h4, hc02, hlam, p1238_1]
                                      · linarith only [h1224, h1270, hlam]
                                    · linarith only [h1223, h1269, hlam]
                                  · linarith only [h1220, h1268, hlam]
                                · linarith only [h1267, h3, hlam]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h2, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h0, h1225, h1235, h1237, hc04, hc45, hlam, hphi, ht0b, ht5b, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                rcases p1238_3 (m.d 0 1) (by simp) with h1359 | h1359
                                · rcases p1238_3 (m.d 0 2) (by simp) with h1360 | h1360
                                  · linarith only [h1360, h5, hlam]
                                  · linarith only [h1360, h4, hlam]
                                · linarith only [h1, h1359, hlam]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                rcases p1238_3 (m.d 0 1) (by simp) with h1365 | h1365
                                · rcases p1238_3 (m.d 0 2) (by simp) with h1366 | h1366
                                  · linarith only [h1366, h5, hlam]
                                  · linarith only [h1220, h1366, hlam]
                                · linarith only [h1365, h3, hlam]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h3, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1220, hlam, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1223, hlam, p1238_0]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [h1224, hlam, p1238_1]
                              · have p1238_0 := h1238c.1
                                have p1238_1 := h1238c.2.1
                                have p1238_2 := h1238c.2.2.1
                                have p1238_3 := h1238c.2.2.2
                                linarith only [hlam, p1238_0]
                            · linarith only [h1233, h1237, h5, hc04, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1232, h1236, h3, h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo0]
                        · linarith only [h1235, hc23, hlam, hphi, ht34, ht45, u5elo3]
                    · linarith only [h1225, h1226, h1232, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h1231, hc13, hlam, hphi, ht34, ht45, u5elo3]
              · linarith only [h1225, h1228, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h1225, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h1224, h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
      · linarith only [h1223, hc03, hlam, hphi, ht34, ht45, u5elo3]
  · linarith only [h1220, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1386 | h1386
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1387 | h1387
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1388 | h1388
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1389 | h1389
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1390 | h1390
          · linarith only [h0, h1385, h1390, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1392 | h1392
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1393 | h1393
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1394 | h1394
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1395 | h1395
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1396 | h1396
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1397 | h1397
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1398 | h1398
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1399 | h1399
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1400 | h1400
                            · rcases h0bigk with h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [hlam, p1401_0]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h0, h1392, h1397, h1400, hc01, hc45, hlam, hphi, ht0b, ht5b, p1401_1]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h0, h1392, h1397, h1400, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1401_1]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                rcases p1401_3 (m.d 0 1) (by simp) with h1405 | h1405
                                · rcases p1401_3 (m.d 0 2) (by simp) with h1406 | h1406
                                  · linarith only [h0, h1406, hlam]
                                  · linarith only [h1385, h1406, hlam]
                                · linarith only [h1405, h2, hlam]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                rcases p1401_3 (m.d 0 1) (by simp) with h1410 | h1410
                                · rcases p1401_3 (m.d 0 2) (by simp) with h1411 | h1411
                                  · linarith only [h0, h1411, hlam]
                                  · linarith only [h1386, h1411, hlam]
                                · linarith only [h1410, h3, hlam]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h0, hlam, p1401_0]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [hlam, p1401_0]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h4, hlam, p1401_0]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h1385, h1397, h1400, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1401_1]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                rcases p1401_3 (m.d 0 1) (by simp) with h1419 | h1419
                                · rcases p1401_3 (m.d 0 2) (by simp) with h1420 | h1420
                                  · rcases p1401_3 (m.d 0 3) (by simp) with h1421 | h1421
                                    · rcases p1401_3 (m.d 0 4) (by simp) with h1422 | h1422
                                      · linarith only [h1385, h1422, hlam]
                                      · linarith only [h1389, h1422, hlam]
                                    · linarith only [h1388, h1421, hlam]
                                  · linarith only [h1386, h1420, hlam]
                                · linarith only [h1419, h3, hlam]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h1, hlam, p1401_1]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h0, h1392, h1397, h1400, hc03, hc45, hlam, hphi, ht0b, ht5b, p1401_1]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [hlam, p1401_0]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                rcases p1401_3 (m.d 0 1) (by simp) with h1431 | h1431
                                · rcases p1401_3 (m.d 0 2) (by simp) with h1432 | h1432
                                  · linarith only [h1432, h4, hlam]
                                  · linarith only [h1385, h1432, hlam]
                                · linarith only [h1431, h2, hlam]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                rcases p1401_3 (m.d 0 1) (by simp) with h1436 | h1436
                                · rcases p1401_3 (m.d 0 2) (by simp) with h1437 | h1437
                                  · linarith only [h1437, h4, hlam]
                                  · linarith only [h1386, h1437, hlam]
                                · linarith only [h1436, h3, hlam]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h2, hlam, p1401_0]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h1385, hlam, p1401_0]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h1387, hlam, p1401_0]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [hlam, p1401_0]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                rcases p1401_3 (m.d 0 1) (by simp) with h1445 | h1445
                                · rcases p1401_3 (m.d 0 2) (by simp) with h1446 | h1446
                                  · rcases p1401_3 (m.d 0 3) (by simp) with h1447 | h1447
                                    · rcases p1401_3 (m.d 0 4) (by simp) with h1448 | h1448
                                      · rcases p1401_3 (m.d 0 5) (by simp) with h1449 | h1449
                                        · linarith only [h1389, h1449, hlam]
                                        · rcases h0emin with h1451 | h1451 | h1451 | h1451 | h1451
                                          · rcases h2bigk with h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c | h1452c
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1392, h1397, h1400, hc02, hc45, hlam, hphi, ht0b, ht5b, p1452_1]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h4, hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1397, h1400, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1452_1]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              rcases p1452_3 (m.d 0 2) (by simp) with h1457 | h1457
                                              · rcases p1452_3 (m.d 1 2) (by simp) with h1458 | h1458
                                                · linarith only [h0, h1458, hlam]
                                                · linarith only [h1393, h1458, hlam]
                                              · linarith only [h1457, hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h0, hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1390, hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h0, h1397, h1400, hc01, hc45, hlam, hphi, ht0b, ht5b, p1452_1]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              rcases p1452_3 (m.d 0 2) (by simp) with h1466 | h1466
                                              · rcases p1452_3 (m.d 1 2) (by simp) with h1467 | h1467
                                                · rcases p1452_3 (m.d 2 3) (by simp) with h1468 | h1468
                                                  · rcases p1452_3 (m.d 2 4) (by simp) with h1469 | h1469
                                                    · linarith only [h1392, h1469, hlam]
                                                    · linarith only [h1399, h1469, hlam]
                                                  · linarith only [h1398, h1468, hlam]
                                                · linarith only [h1467, hlam, p1452_0]
                                              · linarith only [h1386, h1466, hlam]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1385, h1397, h1400, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1452_1]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1392, h1397, h1400, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1452_1]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              rcases p1452_3 (m.d 0 2) (by simp) with h1478 | h1478
                                              · linarith only [h1478, h4, hlam]
                                              · linarith only [h1385, h1478, hlam]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1385, h1393, h3, h4, hlam, p1401_1, p1452_2]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1385, hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1392, hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1397, hlam, p1452_1]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h0, h1392, h1398, h1400, hc01, hc45, hlam, hphi, ht0b, ht5b, p1452_1]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1386, hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1393, hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1398, hlam, p1452_1]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [h1399, hlam, p1452_0]
                                            · have p1452_0 := h1452c.1
                                              have p1452_1 := h1452c.2.1
                                              have p1452_2 := h1452c.2.2.1
                                              have p1452_3 := h1452c.2.2.2
                                              linarith only [hlam, p1452_0]
                                          · linarith only [h1451, h4, hc23, hlam, ht01, ht12]
                                          · rcases h2bigk with h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h4, hc12, hc23, hlam, hphi, p1493_1]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h4, hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1397, h1400, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1493_1]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              rcases p1493_3 (m.d 0 2) (by simp) with h1498 | h1498
                                              · rcases p1493_3 (m.d 1 2) (by simp) with h1499 | h1499
                                                · linarith only [h0, h1499, hlam]
                                                · linarith only [h1393, h1499, hlam]
                                              · linarith only [h1498, hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h0, hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1390, hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h0, h1397, h1400, hc01, hc45, hlam, hphi, ht0b, ht5b, p1493_1]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              rcases p1493_3 (m.d 0 2) (by simp) with h1507 | h1507
                                              · rcases p1493_3 (m.d 1 2) (by simp) with h1508 | h1508
                                                · rcases p1493_3 (m.d 2 3) (by simp) with h1509 | h1509
                                                  · rcases p1493_3 (m.d 2 4) (by simp) with h1510 | h1510
                                                    · linarith only [h1392, h1510, hlam]
                                                    · linarith only [h1399, h1510, hlam]
                                                  · linarith only [h1398, h1509, hlam]
                                                · linarith only [h1508, hlam, p1493_0]
                                              · linarith only [h1386, h1507, hlam]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1385, h1397, h1400, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1493_1]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1392, h1397, h1400, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1493_1]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              rcases p1493_3 (m.d 0 2) (by simp) with h1519 | h1519
                                              · linarith only [h1519, h4, hlam]
                                              · linarith only [h1385, h1519, hlam]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1385, h1393, h3, h4, hlam, p1401_1, p1493_2]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1385, hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1392, hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1397, hlam, p1493_1]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h0, h1392, h1398, h1400, hc01, hc45, hlam, hphi, ht0b, ht5b, p1493_1]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1386, hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1393, hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1398, hlam, p1493_1]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [h1399, hlam, p1493_0]
                                            · have p1493_0 := h1493c.1
                                              have p1493_1 := h1493c.2.1
                                              have p1493_2 := h1493c.2.2.1
                                              have p1493_3 := h1493c.2.2.2
                                              linarith only [hlam, p1493_0]
                                          · linarith only [h1385, h1451, h4, hc23, hlam, ht01, ht12]
                                          · linarith only [h1451, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                                      · linarith only [h1389, h1448, hlam]
                                    · linarith only [h1388, h1447, hlam]
                                  · linarith only [h1386, h1446, hlam]
                                · linarith only [h1445, h3, hlam]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h3, hlam, p1401_0]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h1386, hlam, p1401_1]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h1388, hlam, p1401_0]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [h1389, hlam, p1401_1]
                              · have p1401_0 := h1401c.1
                                have p1401_1 := h1401c.2.1
                                have p1401_2 := h1401c.2.2.1
                                have p1401_3 := h1401c.2.2.2
                                linarith only [hlam, p1401_0]
                            · linarith only [h1400, hc34, hlam, hphi, ht45, u5elo4]
                          · linarith only [h1399, hc24, hlam, hphi, ht45, u5elo4]
                        · linarith only [h1398, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h1387, h1397, h4, hlam]
                    · linarith only [h1396, hc14, hlam, hphi, ht45, u5elo4]
                  · linarith only [h1388, h1395, hc13, hlam, hphi, ht34, ht45, u5elo0]
                · linarith only [h1390, h1392, h1394, hlam]
              · linarith only [h1392, h1393, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h1385, h1392, h4, hc12, hc23, hlam, hphi]
        · linarith only [h1389, hc04, hlam, hphi, ht45, u5elo4]
      · linarith only [h1388, h4, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · linarith only [h1385, h1387, h4, hlam]
  · linarith only [h1385, h1386, hc24, hlam, hphi, ht45, u5elo2]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h0, h1557, h1561, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h0, h1385, h1563, hlam]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [hlam, p1573_0]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 1) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 1) ∧ (m.d 0 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 2) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  rcases p1573_3 (m.d 0 1) (by simp) with h1575 | h1575
  · rcases p1573_3 (m.d 0 2) (by simp) with h1576 | h1576
    · linarith only [h0, h1576, hlam]
    · rcases p1573_3 (m.d 0 3) (by simp) with h1578 | h1578
      · linarith only [h1, h1578, hlam]
      · linarith only [h1578, h4, hlam]
  · linarith only [h0, h1575, hlam]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x2 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 1) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 1) ∧ (m.d 0 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 3) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [h1, h1566, h1572, hc01, hc45, hlam, hphi, ht0b, ht5b, p1573_1]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x3 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 1) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 1) ∧ (m.d 0 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 4) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  rcases p1573_3 (m.d 0 1) (by simp) with h1583 | h1583
  · rcases p1573_3 (m.d 0 2) (by simp) with h1584 | h1584
    · linarith only [h0, h1584, hlam]
    · rcases p1573_3 (m.d 0 3) (by simp) with h1586 | h1586
      · linarith only [h1, h1586, hlam]
      · linarith only [h1558, h1586, hlam]
  · linarith only [h1583, h2, hlam]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x4 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 1) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 1) ∧ (m.d 0 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 5) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  rcases p1573_3 (m.d 0 1) (by simp) with h1590 | h1590
  · rcases p1573_3 (m.d 0 2) (by simp) with h1591 | h1591
    · linarith only [h0, h1591, hlam]
    · linarith only [h1557, h1591, hlam]
  · linarith only [h1590, h3, hlam]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x5 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 2) ∧ (m.d 0 1) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 1) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [h0, hlam, p1573_0]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x6 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 2) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 2) ∧ (m.d 0 2) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 2) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [hlam, p1573_0]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x7 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 2) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 2) ∧ (m.d 0 3) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 3) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [h4, hlam, p1573_0]

set_option maxHeartbeats 6396000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s3_x1_x1_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x8 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1385 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1557 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1558 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1559 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1560 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1561 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1563 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1565 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1566 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1567 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1568 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1569 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h1570 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h1571 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h1572 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h1573c : ((m.d 0 2) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 2) ∧ (m.d 0 4) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 4) ≤ z)))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have p1573_0 := h1573c.1
  have p1573_1 := h1573c.2.1
  have p1573_2 := h1573c.2.2.1
  have p1573_3 := h1573c.2.2.2
  linarith only [h1385, hlam, p1573_1]

end R2N4
