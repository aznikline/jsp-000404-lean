import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_57S5
import Jsp000404.R1LeavesN7_57S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3710000 in
set_option maxHeartbeats 3710000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_0_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h659 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1206 | h1206
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1207 | h1207
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1208 | h1208
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1209 | h1209
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1210 | h1210
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1211 | h1211
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1212 | h1212
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1213 | h1213
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1214 | h1214
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1215 | h1215
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1216 | h1216
                      · linarith only [h1206, h1216, h659, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1218 | h1218
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1219 | h1219
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1220 | h1220
                            · linarith only [h1212, h1216, h1220, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1222 | h1222
                              · linarith only [h1212, h1216, h1218, h1222, hlam]
                              · rcases h1bigk with h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h0, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h659, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1212, h1218, h659, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1224_1, u3elo1]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h659, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1224_1, u3elo1]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  rcases p1224_3 (m.d 0 1) (by simp) with h1230 | h1230
                                  · linarith only [h1230, hlam, p1224_0]
                                  · rcases p1224_3 (m.d 1 2) (by simp) with h1232 | h1232
                                    · rcases p1224_3 (m.d 1 3) (by simp) with h1233 | h1233
                                      · linarith only [h1211, h1233, hlam]
                                      · linarith only [h1233, h659, hlam]
                                    · linarith only [h1232, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h659, hc01, hc12, hlam, hphi, p1224_1]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  rcases p1224_3 (m.d 0 1) (by simp) with h1239 | h1239
                                  · linarith only [h0, h1239, hlam]
                                  · linarith only [h1206, h1239, hlam]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  rcases p1224_3 (m.d 0 1) (by simp) with h1242 | h1242
                                  · linarith only [h0, h1242, hlam]
                                  · linarith only [h1207, h1242, hlam]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1207, h1212, h1216, h1218, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1224_1, u3elo1]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1211, hlam, p1224_1]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  rcases p1224_3 (m.d 0 1) (by simp) with h1248 | h1248
                                  · linarith only [h1248, h659, hlam]
                                  · linarith only [h1206, h1248, hlam]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  rcases p1224_3 (m.d 0 1) (by simp) with h1251 | h1251
                                  · linarith only [h1251, h659, hlam]
                                  · linarith only [h1207, h1251, hlam]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1206, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1212, hlam, p1224_1]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1214, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1216, hlam, p1224_1]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1207, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1213, hlam, p1224_1]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1215, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1207, h1212, h1218, hc34, hlam, hphi, ht0b, ht45, ht5b, p1224_1, u0elo0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [hlam, p1224_0]
                          · linarith only [h1210, h1219, h659, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1209, h1218, h659, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1206, h1212, h1215, h659, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · linarith only [h1206, h1212, h1214, h659, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · linarith only [h1207, h1211, h1213, h659, hlam]
              · linarith only [h0, h1208, h1212, hlam]
            · linarith only [h0, h1206, h1211, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · linarith only [h1207, h1210, h659, hlam]
        · linarith only [h1206, h1209, h659, hlam]
      · linarith only [h0, h1206, h1208, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1274 | h1274
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1275 | h1275
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1276 | h1276
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1277 | h1277
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1278 | h1278
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1279 | h1279
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1280 | h1280
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1281 | h1281
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1282 | h1282
                      · linarith only [h1206, h1207, h1281, h1282, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1284 | h1284
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1285 | h1285
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1286 | h1286
                            · linarith only [h1206, h1207, h1278, h1282, h1286, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1288 | h1288
                              · linarith only [h1206, h1207, h1278, h1282, h1284, h1288, hlam]
                              · rcases h1bigk with h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c | h1290c
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [hlam, p1290_0]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h0, hlam, p1290_0]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h659, hlam, p1290_0]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1207, h1281, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1290_1, u3elo1]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1207, hlam, p1290_0]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  rcases p1290_3 (m.d 0 1) (by simp) with h1296 | h1296
                                  · linarith only [h1296, hlam, p1290_0]
                                  · rcases p1290_3 (m.d 1 2) (by simp) with h1298 | h1298
                                    · rcases p1290_3 (m.d 1 3) (by simp) with h1299 | h1299
                                      · linarith only [h1277, h1299, hlam]
                                      · linarith only [h1299, h659, hlam]
                                    · linarith only [h1298, hlam, p1290_0]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [hlam, p1290_0]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1207, h1281, hc01, hc12, hlam, hphi, p1290_1]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  rcases p1290_3 (m.d 0 1) (by simp) with h1305 | h1305
                                  · linarith only [h0, h1305, hlam]
                                  · linarith only [h1206, h1305, hlam]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1206, h1207, h1278, h1284, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1290_1]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1206, h1278, h1284, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1290_1, u3elo1]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1277, hlam, p1290_1]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [hlam, p1290_0]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  rcases p1290_3 (m.d 0 1) (by simp) with h1312 | h1312
                                  · linarith only [h1312, h659, hlam]
                                  · linarith only [h1206, h1312, hlam]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1206, h1207, h1278, h1284, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1290_1, u3elo1]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1206, hlam, p1290_0]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1278, hlam, p1290_1]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1280, hlam, p1290_0]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [hlam, p1290_0]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1282, hlam, p1290_1]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1206, h1278, h1282, h1284, hc34, hc45, hlam, hphi, p1290_1]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1279, hlam, p1290_1]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [h1281, hlam, p1290_0]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  rcases p1290_3 (m.d 0 1) (by simp) with h1324 | h1324
                                  · linarith only [h1207, h1324, hlam]
                                  · linarith only [h1206, h1324, hlam]
                                · have p1290_0 := h1290c.1
                                  have p1290_1 := h1290c.2.1
                                  have p1290_2 := h1290c.2.2.1
                                  have p1290_3 := h1290c.2.2.2
                                  linarith only [hlam, p1290_0]
                          · linarith only [h1276, h1285, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1275, h1284, h659, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1281, h659, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1206, h1278, h1280, h659, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1332 | h1332
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1333 | h1333
                    · linarith only [h1277, h1279, h1333, hlam]
                    · linarith only [h1276, h1333, h659, hlam]
                  · linarith only [h1206, h1278, h1332, h659, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · linarith only [h0, h1274, h1278, hlam]
            · linarith only [h0, h1206, h1277, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1339 | h1339
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1340 | h1340
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1341 | h1341
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1342 | h1342
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1343 | h1343
                    · linarith only [h1276, h1343, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1206, h1340, h1343, h659, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · linarith only [h1206, h1340, h1342, h659, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1347 | h1347
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1348 | h1348
                    · linarith only [h1206, h1276, h1339, h1340, h1341, h1348, h659, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h1206, h1340, h1348, h659, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                  · linarith only [h1206, h1340, h1347, h659, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · linarith only [h0, h1274, h1340, hlam]
            · linarith only [h0, h1339, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h1206, h1275, h659, hlam]
      · linarith only [h0, h1206, h1274, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1356 | h1356
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1357 | h1357
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1358 | h1358
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1359 | h1359
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1360 | h1360
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1361 | h1361
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1362 | h1362
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1363 | h1363
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1364 | h1364
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1365 | h1365
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1366 | h1366
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1367 | h1367
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1368 | h1368
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1369 | h1369
                              · rcases h1bigk with h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h0, hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h659, hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1206, hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1206, h1362, h1363, h1367, h1369, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1370_1, u3elo1]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  rcases p1370_3 (m.d 0 1) (by simp) with h1376 | h1376
                                  · linarith only [h1376, hlam, p1370_0]
                                  · rcases p1370_3 (m.d 1 2) (by simp) with h1378 | h1378
                                    · rcases p1370_3 (m.d 1 3) (by simp) with h1379 | h1379
                                      · linarith only [h1360, h1379, hlam]
                                      · linarith only [h1379, h659, hlam]
                                    · linarith only [h1378, hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1206, h1363, hc01, hc12, hlam, hphi, p1370_1]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1206, h1356, h1362, h1367, h1369, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1370_1]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  rcases p1370_3 (m.d 0 1) (by simp) with h1386 | h1386
                                  · linarith only [h0, h1386, hlam]
                                  · linarith only [h1356, h1386, hlam]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1356, h1362, h1367, h1369, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1370_1, u3elo1]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1360, hlam, p1370_1]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1206, h1356, h1362, h1367, h1369, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1370_1, u3elo1]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  rcases p1370_3 (m.d 0 1) (by simp) with h1393 | h1393
                                  · linarith only [h1393, h659, hlam]
                                  · linarith only [h1356, h1393, hlam]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1356, h1362, h1363, h1367, h1369, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1370_1, u3elo1]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1361, hlam, p1370_1]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1363, hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  rcases p1370_3 (m.d 0 1) (by simp) with h1400 | h1400
                                  · linarith only [h1206, h1400, hlam]
                                  · linarith only [h1356, h1400, hlam]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1356, hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1362, hlam, p1370_1]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1364, hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [h1365, hlam, p1370_0]
                                · have p1370_0 := h1370c.1
                                  have p1370_1 := h1370c.2.1
                                  have p1370_2 := h1370c.2.2.1
                                  have p1370_3 := h1370c.2.2.2
                                  linarith only [hlam, p1370_0]
                              · linarith only [h1356, h1365, h1369, h659, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h1206, h1356, h1363, h1365, h1366, h1368, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1359, h1366, h1367, h659, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · linarith only [h1358, h1366, h659, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1206, h1356, h1365, hlam]
                    · linarith only [h1206, h1363, h1364, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1356, h1358, h1362, h1363, h659, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h1356, h1360, h1362, h659, hlam]
              · linarith only [h1357, h1360, h1361, h659, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1356, h1360, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
          · linarith only [h1356, h1359, h659, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1419 | h1419
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1420 | h1420
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1421 | h1421
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1422 | h1422
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1423 | h1423
                  · linarith only [h1358, h1419, h1423, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h1356, h1422, h1423, h659, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h1356, h1420, h1422, h659, hlam]
              · linarith only [h1357, h1420, h1421, h659, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1356, h1420, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
          · linarith only [h1356, h1419, h659, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1430 | h1430
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1431 | h1431
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1432 | h1432
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1433 | h1433
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1434 | h1434
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1435 | h1435
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1436 | h1436
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1437 | h1437
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1438 | h1438
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1439 | h1439
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1440 | h1440
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1441 | h1441
                              · rcases h1bigk with h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h0, hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h659, hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h1206, hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h0, h1357, h1433, h1435, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1442_1, u3elo1]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  rcases p1442_3 (m.d 0 1) (by simp) with h1448 | h1448
                                  · linarith only [h1448, hlam, p1442_0]
                                  · rcases p1442_3 (m.d 1 2) (by simp) with h1450 | h1450
                                    · rcases p1442_3 (m.d 1 3) (by simp) with h1451 | h1451
                                      · linarith only [h1432, h1451, hlam]
                                      · linarith only [h1451, h659, hlam]
                                    · linarith only [h1450, hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h0, h1357, h1433, h1435, hc01, hc12, hlam, hphi, p1442_1]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h0, h1356, h1357, h1433, h1434, h1439, h1441, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1442_1]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h0, h1356, h1357, h1432, h1438, hlam, p1442_2]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h1356, h1434, h1439, h1441, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1442_1, u3elo1]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h1432, hlam, p1442_1]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h0, h1356, h1357, h1433, h1434, h1439, h1441, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1442_1, u3elo1]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  rcases p1442_3 (m.d 0 1) (by simp) with h1463 | h1463
                                  · linarith only [h1463, h659, hlam]
                                  · linarith only [h1356, h1463, hlam]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h1356, h1434, h1435, h1439, h1441, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1442_1, u3elo1]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h1433, hlam, p1442_1]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h1435, hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  rcases p1442_3 (m.d 0 1) (by simp) with h1470 | h1470
                                  · linarith only [h1206, h1470, hlam]
                                  · linarith only [h1356, h1470, hlam]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h1356, hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h1434, hlam, p1442_1]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h1436, hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [h1437, hlam, p1442_0]
                                · have p1442_0 := h1442c.1
                                  have p1442_1 := h1442c.2.1
                                  have p1442_2 := h1442c.2.2.1
                                  have p1442_3 := h1442c.2.2.2
                                  linarith only [hlam, p1442_0]
                              · linarith only [h0, h1356, h1357, h1432, h1437, h1438, h1441, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h1356, h1357, h1437, h1440, hlam]
                          · linarith only [h0, h1357, h1438, h1439, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1430, h1438, h659, hc23, hlam, hphi, u3elo1]
                      · linarith only [h0, h1356, h1357, h1433, h1437, hlam]
                    · linarith only [h0, h1357, h1433, h1435, h1436, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1430, h1435, h659, hlam]
                · linarith only [h0, h1357, h1433, h1434, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1486 | h1486
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1487 | h1487
                  · linarith only [h1432, h1433, h1487, hlam]
                  · linarith only [h1430, h1487, h659, hlam]
                · linarith only [h0, h1356, h1486, hlam]
            · linarith only [h0, h1432, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h0, h1356, h1357, h1430, h1431, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1493 | h1493
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1494 | h1494
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1495 | h1495
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1496 | h1496
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1497 | h1497
                  · linarith only [h1430, h1497, h659, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1356, h1496, h1497, h659, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h0, h1357, h1495, h1496, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1501 | h1501
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1502 | h1502
                  · linarith only [h1356, h1430, h1501, h1502, h659, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h1356, h1501, h1502, h659, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h1356, h1501, h659, hc12, hlam, hphi, ht23, u3elo1]
            · linarith only [h0, h1494, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h1356, h1493, h659, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1508 | h1508
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1509 | h1509
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1510 | h1510
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1511 | h1511
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1512 | h1512
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1513 | h1513
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1514 | h1514
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1515 | h1515
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1516 | h1516
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1517 | h1517
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1518 | h1518
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1519 | h1519
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1520 | h1520
                              · rcases h1bigk with h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h0, hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h659, hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1206, hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1356, hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  rcases p1521_3 (m.d 0 1) (by simp) with h1527 | h1527
                                  · linarith only [h1527, hlam, p1521_0]
                                  · rcases p1521_3 (m.d 1 2) (by simp) with h1529 | h1529
                                    · rcases p1521_3 (m.d 1 3) (by simp) with h1530 | h1530
                                      · linarith only [h1511, h1530, hlam]
                                      · linarith only [h1530, h659, hlam]
                                    · linarith only [h1529, hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1356, h1514, h1516, hc01, hc12, hlam, hphi, p1521_1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1206, hc01, hc12, hlam, hphi, p1521_1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1356, hc01, hc12, hlam, hphi, p1521_1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p1521_1, u3elo1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1511, hlam, p1521_1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1206, hc01, hlam, hphi, ht12, ht23, p1521_1, u3elo1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1356, hc01, hlam, hphi, ht12, ht23, p1521_1, u3elo1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1514, hc01, hlam, hphi, ht12, ht23, p1521_1, u3elo1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1512, hlam, p1521_1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1514, hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1356, h1514, hc01, hlam, hphi, ht12, ht23, p1521_1, u3elo1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1515, hc01, hlam, hphi, ht12, ht23, p1521_1, u3elo1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1513, hlam, p1521_1]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1515, hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [h1516, hlam, p1521_0]
                                · have p1521_0 := h1521c.1
                                  have p1521_1 := h1521c.2.1
                                  have p1521_2 := h1521c.2.2.1
                                  have p1521_3 := h1521c.2.2.2
                                  linarith only [hlam, p1521_0]
                              · linarith only [h1508, h1519, h1520, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1554 | h1554
                              · linarith only [h1517, h1519, h1554, hlam]
                              · rcases h1bigk with h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h0, hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h659, hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1206, hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1356, hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  rcases p1556_3 (m.d 0 1) (by simp) with h1562 | h1562
                                  · linarith only [h1562, hlam, p1556_0]
                                  · rcases p1556_3 (m.d 1 2) (by simp) with h1564 | h1564
                                    · rcases p1556_3 (m.d 1 3) (by simp) with h1565 | h1565
                                      · linarith only [h1511, h1565, hlam]
                                      · linarith only [h1565, h659, hlam]
                                    · linarith only [h1564, hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1514, h1516, h1517, h1519, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1556_1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1516, h1517, h1519, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1556_1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1356, hc01, hc12, hlam, hphi, p1556_1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p1556_1, u3elo1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1511, hlam, p1556_1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1516, h1517, h1519, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1556_1, u3elo1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1356, hc01, hlam, hphi, ht12, ht23, p1556_1, u3elo1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1514, hc01, hlam, hphi, ht12, ht23, p1556_1, u3elo1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1512, hlam, p1556_1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1514, hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1356, h1514, hc01, hlam, hphi, ht12, ht23, p1556_1, u3elo1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1515, hc01, hlam, hphi, ht12, ht23, p1556_1, u3elo1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1513, hlam, p1556_1]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1515, hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [h1516, hlam, p1556_0]
                                · have p1556_0 := h1556c.1
                                  have p1556_1 := h1556c.2.1
                                  have p1556_2 := h1556c.2.2.1
                                  have p1556_3 := h1556c.2.2.2
                                  linarith only [hlam, p1556_0]
                          · linarith only [h1510, h1518, h659, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1509, h1517, h659, hc23, hlam, hphi, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1590 | h1590
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1591 | h1591
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1592 | h1592
                            · linarith only [h1206, h1516, h1592, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1594 | h1594
                              · linarith only [h1206, h1509, h1516, h1594, h659, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases h1bigk with h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [hlam, p1596_0]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h0, hlam, p1596_0]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h659, hlam, p1596_0]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1206, hlam, p1596_0]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1356, hlam, p1596_0]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  rcases p1596_3 (m.d 0 1) (by simp) with h1602 | h1602
                                  · linarith only [h1602, hlam, p1596_0]
                                  · rcases p1596_3 (m.d 1 2) (by simp) with h1604 | h1604
                                    · rcases p1596_3 (m.d 1 3) (by simp) with h1605 | h1605
                                      · linarith only [h1511, h1605, hlam]
                                      · linarith only [h1605, h659, hlam]
                                    · linarith only [h1604, hlam, p1596_0]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [hlam, p1596_0]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h659, hc01, hc12, hlam, hphi, p1596_1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1206, hc01, hc12, hlam, hphi, p1596_1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1356, hc01, hc12, hlam, hphi, p1596_1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p1596_1, u3elo1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1511, hlam, p1596_1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [hlam, p1596_0]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1206, hc01, hlam, hphi, ht12, ht23, p1596_1, u3elo1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1356, hc01, hlam, hphi, ht12, ht23, p1596_1, u3elo1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1516, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1596_1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1512, hlam, p1596_1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1514, hlam, p1596_0]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [hlam, p1596_0]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1516, hlam, p1596_1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1515, hc01, hlam, hphi, ht12, ht23, p1596_1, u3elo1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1513, hlam, p1596_1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1515, hlam, p1596_0]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [h1206, h1515, hc01, hlam, hphi, ht12, ht23, p1596_1, u3elo1]
                                · have p1596_0 := h1596c.1
                                  have p1596_1 := h1596c.2.1
                                  have p1596_2 := h1596c.2.2.1
                                  have p1596_3 := h1596c.2.2.2
                                  linarith only [hlam, p1596_0]
                          · linarith only [h1510, h1591, h659, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1509, h1590, h659, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1510, h1515, h659, hlam]
                  · linarith only [h1509, h1514, h659, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1632 | h1632
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1633 | h1633
                    · linarith only [h1511, h1513, h1633, hlam]
                    · linarith only [h1510, h1633, h659, hlam]
                  · linarith only [h1509, h1632, h659, hlam]
              · linarith only [h0, h1508, h1512, hlam]
            · linarith only [h0, h1511, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1639 | h1639
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1640 | h1640
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1641 | h1641
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1642 | h1642
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1643 | h1643
                    · linarith only [h1510, h1643, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1643, h659, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1509, h1642, h659, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1647 | h1647
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1648 | h1648
                    · linarith only [h1509, h1510, h1648, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                    · linarith only [h1648, h659, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1509, h1647, h659, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h1508, h1639, h1640, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1639, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1654 | h1654
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1655 | h1655
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1656 | h1656
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1657 | h1657
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1658 | h1658
                  · linarith only [h1509, h1658, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1658, h659, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1661 | h1661
                  · linarith only [h1509, h1654, h1655, h1657, h1661, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h1661, h659, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h1508, h1655, h1656, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1655, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1666 | h1666
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1667 | h1667
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1668 | h1668
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1669 | h1669
                  · linarith only [h1509, h1669, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1669, h659, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1672 | h1672
                  · linarith only [h1509, h1672, h659, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1672, h659, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · linarith only [h0, h1508, h1667, hlam]
            · linarith only [h0, h1666, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1677 | h1677
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1678 | h1678
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1679 | h1679
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1680 | h1680
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1681 | h1681
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1682 | h1682
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1683 | h1683
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1684 | h1684
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1685 | h1685
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1686 | h1686
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1687 | h1687
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1688 | h1688
                              · rcases h1bigk with h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c | h1689c
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h0, hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h659, hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1206, hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1356, hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  rcases p1689_3 (m.d 0 1) (by simp) with h1695 | h1695
                                  · linarith only [h1695, hlam, p1689_0]
                                  · rcases p1689_3 (m.d 1 2) (by simp) with h1697 | h1697
                                    · rcases p1689_3 (m.d 1 3) (by simp) with h1698 | h1698
                                      · linarith only [h1679, h1698, hlam]
                                      · linarith only [h1698, h659, hlam]
                                    · linarith only [h1697, hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h0, h1508, h1680, h1682, hc01, hc12, hlam, hphi, p1689_1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h0, h1508, h1680, hc01, hc12, hlam, hphi, p1689_1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1356, hc01, hc12, hlam, hphi, p1689_1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p1689_1, u3elo1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1679, hlam, p1689_1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h0, h1508, h1680, hc01, hlam, hphi, ht12, ht23, p1689_1, u3elo1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1356, hc01, hlam, hphi, ht12, ht23, p1689_1, u3elo1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1682, hc01, hlam, hphi, ht12, ht23, p1689_1, u3elo1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1680, hlam, p1689_1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1682, hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1356, h1682, hc01, hlam, hphi, ht12, ht23, p1689_1, u3elo1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1683, hc01, hlam, hphi, ht12, ht23, p1689_1, u3elo1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1681, hlam, p1689_1]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1683, hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [h1684, hlam, p1689_0]
                                · have p1689_0 := h1689c.1
                                  have p1689_1 := h1689c.2.1
                                  have p1689_2 := h1689c.2.2.1
                                  have p1689_3 := h1689c.2.2.2
                                  linarith only [hlam, p1689_0]
                              · rcases h1bigk with h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c | h1721c
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h0, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h659, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1206, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1356, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  rcases p1721_3 (m.d 0 1) (by simp) with h1727 | h1727
                                  · linarith only [h1727, hlam, p1721_0]
                                  · rcases p1721_3 (m.d 1 2) (by simp) with h1729 | h1729
                                    · rcases p1721_3 (m.d 1 3) (by simp) with h1730 | h1730
                                      · linarith only [h1679, h1730, hlam]
                                      · linarith only [h1730, h659, hlam]
                                    · linarith only [h1729, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1679, h1685, h1687, h1688, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1206, hc01, hc12, hlam, hphi, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1356, hc01, hc12, hlam, hphi, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p1721_1, u3elo1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1679, hlam, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1680, h1687, h1688, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1721_1, u3elo1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1356, hc01, hlam, hphi, ht12, ht23, p1721_1, u3elo1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1682, hc01, hlam, hphi, ht12, ht23, p1721_1, u3elo1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1680, hlam, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1682, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1356, h1682, hc01, hlam, hphi, ht12, ht23, p1721_1, u3elo1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1683, hc01, hlam, hphi, ht12, ht23, p1721_1, u3elo1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1681, hlam, p1721_1]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1683, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [h1684, hlam, p1721_0]
                                · have p1721_0 := h1721c.1
                                  have p1721_1 := h1721c.2.1
                                  have p1721_2 := h1721c.2.2.1
                                  have p1721_3 := h1721c.2.2.2
                                  linarith only [hlam, p1721_0]
                            · linarith only [h0, h1508, h1682, h1684, h1687, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1678, h1686, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1677, h1685, h659, hc23, hlam, hphi, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1756 | h1756
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1757 | h1757
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1758 | h1758
                            · linarith only [h1206, h1684, h1758, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1760 | h1760
                              · linarith only [h0, h1508, h1677, h1680, h1684, h1760, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · rcases h1bigk with h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c | h1762c
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [hlam, p1762_0]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h0, hlam, p1762_0]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h659, hlam, p1762_0]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1206, hlam, p1762_0]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1356, hlam, p1762_0]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  rcases p1762_3 (m.d 0 1) (by simp) with h1768 | h1768
                                  · linarith only [h1768, hlam, p1762_0]
                                  · rcases p1762_3 (m.d 1 2) (by simp) with h1770 | h1770
                                    · rcases p1762_3 (m.d 1 3) (by simp) with h1771 | h1771
                                      · linarith only [h1679, h1771, hlam]
                                      · linarith only [h1771, h659, hlam]
                                    · linarith only [h1770, hlam, p1762_0]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [hlam, p1762_0]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h659, hc01, hc12, hlam, hphi, p1762_1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h0, h1508, h1680, hc01, hc12, hlam, hphi, p1762_1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1356, hc01, hc12, hlam, hphi, p1762_1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [hc01, hlam, hphi, ht12, ht23, p1762_1, u3elo1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1679, hlam, p1762_1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [hlam, p1762_0]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h0, h1508, h1680, hc01, hlam, hphi, ht12, ht23, p1762_1, u3elo1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h0, h1508, h1681, h1758, hc01, hlam, hphi, ht12, ht23, p1762_1, u3elo1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1684, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1762_1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1680, hlam, p1762_1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1682, hlam, p1762_0]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [hlam, p1762_0]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1684, hlam, p1762_1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1683, hc01, hlam, hphi, ht12, ht23, p1762_1, u3elo1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1681, hlam, p1762_1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1683, hlam, p1762_0]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [h1206, h1683, hc01, hlam, hphi, ht12, ht23, p1762_1, u3elo1]
                                · have p1762_0 := h1762c.1
                                  have p1762_1 := h1762c.2.1
                                  have p1762_2 := h1762c.2.2.1
                                  have p1762_3 := h1762c.2.2.2
                                  linarith only [hlam, p1762_0]
                          · linarith only [h1678, h1757, h659, hc23, hlam, hphi, u3elo1]
                        · linarith only [h1677, h1756, h659, hc23, hlam, hphi, u3elo1]
                    · linarith only [h1678, h1683, h659, hlam]
                  · linarith only [h1677, h1682, h659, hlam]
                · linarith only [h0, h1508, h1680, h1681, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1799 | h1799
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1800 | h1800
                  · linarith only [h1679, h1680, h1800, hlam]
                  · linarith only [h1677, h1800, h659, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1803 | h1803
                  · linarith only [h1679, h1680, h1803, hlam]
                  · linarith only [h1677, h1803, h659, hlam]
            · linarith only [h0, h1679, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1807 | h1807
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1808 | h1808
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1809 | h1809
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1810 | h1810
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1811 | h1811
                    · linarith only [h1678, h1811, hc03, hlam, hphi, u3elo1]
                    · linarith only [h1811, h659, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h1677, h1810, h659, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h1508, h1808, h1809, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1816 | h1816
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1817 | h1817
                  · linarith only [h1807, h1808, h1817, hlam]
                  · linarith only [h1677, h1678, h1817, hc13, hlam, hphi, u3elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1820 | h1820
                  · linarith only [h1807, h1808, h1820, hlam]
                  · linarith only [h1677, h1678, h1820, hc13, hlam, hphi, u3elo4]
            · linarith only [h0, h1807, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1824 | h1824
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1825 | h1825
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1826 | h1826
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1827 | h1827
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1828 | h1828
                  · linarith only [h1677, h1824, h1828, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h1828, h659, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h1508, h1826, h1827, hc02, hc25, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1832 | h1832
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1833 | h1833
                  · linarith only [h1677, h1824, h1833, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h1833, h659, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1836 | h1836
                  · linarith only [h1677, h1824, h1836, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                  · linarith only [h1836, h659, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h0, h1825, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1840 | h1840
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1841 | h1841
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1842 | h1842
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1843 | h1843
                  · linarith only [h1677, h1843, hc03, hlam, hphi, u3elo1]
                  · linarith only [h1843, h659, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · linarith only [h0, h1508, h1841, h1842, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1847 | h1847
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1848 | h1848
                  · linarith only [h1677, h1848, h659, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1848, h659, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1851 | h1851
                  · linarith only [h1677, h1851, h659, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h1851, h659, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h0, h1840, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 3710000 in
set_option maxHeartbeats 3710000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h659 | h659
  · exact r1l7_20_11_13_14_M_LI_L_I_L_0_L_I_x1_x0 m hb0 hb1 hb3 hb4 h0 h659
  · exact r1l7_20_11_13_14_M_LI_L_I_L_0_L_I_x1_x1 m hb0 hb1 hb3 hb4 h0 h659

set_option maxHeartbeats 3710000 in
set_option maxHeartbeats 3710000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_M_LI_L_I_L_0_L_I_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_M_LI_L_I_L_0_L_I_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
