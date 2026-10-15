import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1211 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1212 | h1212
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1213 | h1213
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1214 | h1214
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1215 | h1215
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1216 | h1216
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1217 | h1217
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1218 | h1218
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1219 | h1219
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1220 | h1220
                  · linarith only [h0, h1211, h1220, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1222 | h1222
                    · linarith only [h0, h1212, h1220, h1222, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h1211, h1215, h1222, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h1219, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h1218, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h1211, h1217, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1228 | h1228
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1229 | h1229
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1230 | h1230
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1231 | h1231
                  · linarith only [h0, h1211, h1231, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1233 | h1233
                    · linarith only [h0, h1212, h1231, h1233, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h1211, h1215, h1228, h1233, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h1230, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h1229, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h1211, h1228, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1239 | h1239
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1240 | h1240
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1241 | h1241
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1242 | h1242
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1243 | h1243
                  · linarith only [h0, h1211, h1243, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1245 | h1245
                    · linarith only [h0, h1212, h1215, h1243, h1245, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1247 | h1247
                      · linarith only [h0, h1212, h1247, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h1212, h1239, h1243, h1247, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h1242, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h1241, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h1211, h1240, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1253 | h1253
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1254 | h1254
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1255 | h1255
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1256 | h1256
                  · linarith only [h0, h1211, h1256, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1258 | h1258
                    · linarith only [h1211, h1215, h1258, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1260 | h1260
                      · linarith only [h1212, h1239, h1260, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1262 | h1262
                        · linarith only [h1253, h1256, h1262, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1264 | h1264
                          · linarith only [h1215, h1253, h1264, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1266 | h1266
                            · linarith only [h1239, h1254, h1266, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1268 | h1268
                              · rcases h5bigk with h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c | h1269c
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [hlam, p1269_0]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h0, h1213, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1269_1, u2elo1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h0, h1213, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1269_1, u2elo1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1215, hlam, p1269_0]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1239, hlam, p1269_0]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1213, hlam, p1269_0]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [hlam, p1269_0]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p1269_1, u1elo4]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1258, hlam, p1269_0]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1260, hlam, p1269_0]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1214, hlam, p1269_1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1255, hlam, p1269_1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [hlam, p1269_0]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1264, hlam, p1269_1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1266, hlam, p1269_0]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1211, h1215, h1253, hc23, hc35, hlam, hphi, p1269_1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1253, h1258, hc23, hc35, hlam, hphi, p1269_1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1264, hc23, hc35, hlam, hphi, p1269_1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [hlam, p1269_0]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1212, h1239, h1253, h1256, h1268, hc23, hc34, hlam, hphi, p1269_1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1212, h1239, h1253, h1256, hc23, hc45, hlam, hphi, ht34, p1269_1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1253, h1256, h1260, hc23, hc45, hlam, hphi, ht34, p1269_1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1262, h1266, hc23, hc45, hlam, hphi, ht34, p1269_1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [h1268, hlam, p1269_1]
                                · have p1269_0 := h1269c.1
                                  have p1269_1 := h1269c.2.1
                                  have p1269_2 := h1269c.2.2.1
                                  have p1269_3 := h1269c.2.2.2
                                  linarith only [hlam, p1269_0]
                              · rcases h5bigk with h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h0, h1213, h1253, h1256, h1260, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1295_1, u2elo1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h0, h1213, h1262, h1266, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1295_1, u2elo1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1215, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1239, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1213, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1262, h1266, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1295_1, u1elo4]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1258, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1260, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1214, hlam, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1255, hlam, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1264, hlam, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1266, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1214, h1262, h1266, h1268, hc23, hc45, hlam, hphi, ht34, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1255, h1262, h1266, h1268, hc23, hc45, hlam, hphi, ht34, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1262, h1266, h1268, hc23, hc45, hlam, hphi, ht34, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1268, hlam, p1295_0]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1212, h1239, h1253, h1256, hc23, hc45, hlam, hphi, ht34, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1255, h1262, h1266, hc23, hc45, hlam, hphi, ht34, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1262, h1266, hc23, hc45, hlam, hphi, ht34, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [h1211, h1215, h1253, hc23, hc45, hlam, hphi, ht34, p1295_1]
                                · have p1295_0 := h1295c.1
                                  have p1295_1 := h1295c.2.1
                                  have p1295_2 := h1295c.2.2.1
                                  have p1295_3 := h1295c.2.2.2
                                  linarith only [hlam, p1295_0]
                · linarith only [h0, h1255, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h1211, h1253, h1254, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h0, h1253, hc01, hlam, hphi, ht12, u2elo2]
      · linarith only [h0, h1213, h1214, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1325 | h1325
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1326 | h1326
        · linarith only [h1211, h1213, h1326, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1328 | h1328
          · linarith only [h1212, h1213, h1328, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1330 | h1330
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1331 | h1331
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1332 | h1332
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1333 | h1333
                  · linarith only [h1211, h1213, h1332, h1333, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1335 | h1335
                    · linarith only [h1212, h1213, h1326, h1332, h1333, h1335, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1337 | h1337
                      · linarith only [h1212, h1213, h1328, h1332, h1337, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1339 | h1339
                        · linarith only [h1330, h1333, h1339, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1341 | h1341
                          · linarith only [h1212, h1213, h1330, h1333, h1335, h1341, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1343 | h1343
                            · linarith only [h1213, h1337, h1343, hc01, hlam, hphi, ht12, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1345 | h1345
                              · linarith only [h1212, h1213, h1330, h1333, h1337, h1345, hc23, hc34, hlam, hphi]
                              · rcases h5bigk with h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c | h1347c
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [hlam, p1347_0]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1213, hlam, p1347_1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1325, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1347_1, u2elo0]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1326, hlam, p1347_0]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1328, hlam, p1347_0]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1347_1, u1elo4]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [hlam, p1347_0]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1332, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1347_1, u2elo1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1335, hlam, p1347_0]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1337, hlam, p1347_0]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1325, hlam, p1347_1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1332, hlam, p1347_1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [hlam, p1347_0]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1341, hlam, p1347_1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1343, hlam, p1347_0]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1212, h1213, h1330, h1333, hc23, hc35, hlam, hphi, p1347_1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1212, h1213, h1330, h1333, h1345, hc23, hc45, hlam, hphi, ht34, p1347_1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1341, h1345, hc23, hc45, hlam, hphi, ht34, p1347_1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [hlam, p1347_0]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1345, hlam, p1347_0]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1212, h1213, h1330, h1333, hc23, hc45, hlam, hphi, ht34, p1347_1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1212, h1213, h1330, h1333, hc23, hc45, hlam, hphi, ht34, p1347_1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1341, hc23, hc45, hlam, hphi, ht34, p1347_1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [h1211, h1326, h1330, hc23, hc45, hlam, hphi, ht34, p1347_1]
                                · have p1347_0 := h1347c.1
                                  have p1347_1 := h1347c.2.1
                                  have p1347_2 := h1347c.2.2.1
                                  have p1347_3 := h1347c.2.2.2
                                  linarith only [hlam, p1347_0]
                · linarith only [h0, h1332, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h1211, h1330, h1331, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h0, h1330, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1376 | h1376
        · linarith only [h0, h1211, h1325, h1376, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1378 | h1378
          · linarith only [h0, h1212, h1325, h1378, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1380 | h1380
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1381 | h1381
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1382 | h1382
                · linarith only [h0, h1325, h1382, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1211, h1380, h1382, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h0, h1211, h1380, h1381, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h0, h1380, hc01, hlam, hphi, ht12, u2elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1387 | h1387
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1388 | h1388
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1389 | h1389
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1390 | h1390
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1391 | h1391
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1392 | h1392
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1393 | h1393
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1394 | h1394
                  · linarith only [h1211, h1212, h1392, h1394, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1396 | h1396
                    · linarith only [h1211, h1212, h1392, h1396, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h1211, h1212, h1389, h1391, h1392, h1396, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h1212, h1392, h1393, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h1392, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h1211, h1391, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h1212, h1387, h1390, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1403 | h1403
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1404 | h1404
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1405 | h1405
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1406 | h1406
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1407 | h1407
                  · linarith only [h1211, h1212, h1405, h1407, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1409 | h1409
                    · linarith only [h1211, h1212, h1389, h1405, h1409, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1411 | h1411
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1412 | h1412
                        · linarith only [h1212, h1387, h1404, h1407, h1409, h1412, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1414 | h1414
                          · linarith only [h1211, h1389, h1404, h1414, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1416 | h1416
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1417 | h1417
                              · rcases h5bigk with h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c | h1418c
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [hlam, p1418_0]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1212, h1387, h1405, h1409, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1418_1, u2elo1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1212, h1387, h1405, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1418_1, u2elo1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1389, hlam, p1418_0]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1212, h1387, h1405, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1418_1, u2elo1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1387, hlam, p1418_0]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [hlam, p1418_0]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1416, hc45, hlam, hphi, ht01, ht0b, ht5b, p1418_1, u1elo4]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1409, hlam, p1418_0]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1212, h1387, h1405, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1418_1, u2elo1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1388, hlam, p1418_1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1406, hlam, p1418_1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [hlam, p1418_0]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1414, hlam, p1418_1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1418_1, u2elo4]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1211, h1389, h1404, hc23, hc35, hlam, hphi, p1418_1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1404, h1409, hc23, hc35, hlam, hphi, p1418_1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1414, hc23, hc35, hlam, hphi, p1418_1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [hlam, p1418_0]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  rcases p1418_3 (m.d 0 5) (by simp) with h1438 | h1438
                                  · linarith only [h1389, h1438, hlam]
                                  · linarith only [h1403, h1438, hlam]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1403, hlam, p1418_1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1411, hlam, p1418_1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1416, hlam, p1418_1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [h1417, hlam, p1418_1]
                                · have p1418_0 := h1418c.1
                                  have p1418_1 := h1418c.2.1
                                  have p1418_2 := h1418c.2.2.1
                                  have p1418_3 := h1418c.2.2.2
                                  linarith only [hlam, p1418_0]
                              · linarith only [h1212, h1403, h1404, h1405, h1407, h1417, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h1212, h1387, h1405, h1411, h1416, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h1211, h1212, h1404, h1411, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1212, h1405, h1406, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h1211, h1404, h1405, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h0, h1404, hc01, hlam, hphi, ht12, u2elo2]
          · linarith only [h1212, h1387, h1403, hlam]
      · linarith only [h0, h1387, h1388, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1454 | h1454
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1455 | h1455
        · linarith only [h1211, h1387, h1455, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1457 | h1457
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1458 | h1458
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1459 | h1459
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1460 | h1460
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1461 | h1461
                  · linarith only [h1211, h1212, h1459, h1461, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1463 | h1463
                    · linarith only [h1211, h1212, h1455, h1459, h1463, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1465 | h1465
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1466 | h1466
                        · linarith only [h1211, h1387, h1458, h1461, h1465, h1466, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1468 | h1468
                          · linarith only [h1211, h1387, h1458, h1463, h1468, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1470 | h1470
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1471 | h1471
                              · rcases h5bigk with h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c | h1472c
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [hlam, p1472_0]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1387, hlam, p1472_1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1454, h1470, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1472_1, u2elo0]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1455, hlam, p1472_0]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1212, h1457, h1459, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1472_1, u2elo1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1459, h1465, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1472_1, u2elo1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [hlam, p1472_0]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1459, h1465, h1470, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1472_1, u2elo1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1463, hlam, p1472_0]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1459, h1465, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1472_1, u2elo1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1454, hlam, p1472_1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1460, hlam, p1472_1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [hlam, p1472_0]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1468, hlam, p1472_1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1472_1, u2elo4]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1211, h1387, h1458, hc23, hc35, hlam, hphi, p1472_1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1211, h1387, h1458, hc23, hc35, hlam, hphi, p1472_1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1468, hc23, hc35, hlam, hphi, p1472_1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [hlam, p1472_0]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  rcases p1472_3 (m.d 0 5) (by simp) with h1492 | h1492
                                  · linarith only [h1455, h1492, hlam]
                                  · linarith only [h1457, h1492, hlam]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1457, hlam, p1472_1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1465, hlam, p1472_1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1470, hlam, p1472_1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [h1471, hlam, p1472_1]
                                · have p1472_0 := h1472c.1
                                  have p1472_1 := h1472c.2.1
                                  have p1472_2 := h1472c.2.2.1
                                  have p1472_3 := h1472c.2.2.2
                                  linarith only [hlam, p1472_0]
                              · linarith only [h1212, h1457, h1458, h1459, h1461, h1471, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1501 | h1501
                              · rcases h5bigk with h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1387, hlam, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1387, h1459, h1465, h1466, h1470, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1502_1, u2elo1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1455, hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1387, h1459, h1465, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1502_1, u2elo1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1459, h1465, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1502_1, u2elo1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1459, h1465, h1466, h1470, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1502_1, u2elo1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1463, hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1459, h1465, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1502_1, u2elo1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1454, hlam, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1460, hlam, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1468, hlam, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1470, hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1387, h1501, hc01, hc34, hlam, hphi, ht12, ht23, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1211, h1387, h1458, h1501, hc23, hc34, hlam, hphi, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1466, h1470, h1501, hc23, hc34, hlam, hphi, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [hlam, p1502_0]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1466, h1470, h1501, hc23, hc34, hlam, hphi, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1457, hlam, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1465, hlam, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1466, h1470, hc23, hc45, hlam, hphi, ht34, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [h1501, hlam, p1502_1]
                                · have p1502_0 := h1502c.1
                                  have p1502_1 := h1502c.2.1
                                  have p1502_2 := h1502c.2.2.1
                                  have p1502_3 := h1502c.2.2.2
                                  linarith only [hlam, p1502_0]
                              · linarith only [h1212, h1457, h1458, h1459, h1461, h1501, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1211, h1212, h1458, h1465, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h1211, h1458, h1460, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h0, h1211, h1458, h1459, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h0, h1458, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1533 | h1533
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1534 | h1534
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1535 | h1535
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1536 | h1536
                  · linarith only [h1211, h1212, h1534, h1536, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1538 | h1538
                    · linarith only [h1211, h1212, h1534, h1538, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1540 | h1540
                      · linarith only [h1212, h1457, h1534, h1540, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h1211, h1212, h1533, h1540, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h1454, h1535, hlam]
              · linarith only [h0, h1211, h1533, h1534, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h0, h1211, h1533, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1546 | h1546
        · linarith only [h1211, h1387, h1546, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1548 | h1548
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1549 | h1549
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1550 | h1550
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1551 | h1551
                · linarith only [h0, h1211, h1454, h1549, h1551, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h1211, h1549, h1551, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h0, h1211, h1549, h1550, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h0, h1549, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1556 | h1556
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1557 | h1557
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1558 | h1558
                · linarith only [h0, h1211, h1454, h1556, h1558, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h1211, h1556, h1558, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h0, h1211, h1556, h1557, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
            · linarith only [h0, h1556, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
