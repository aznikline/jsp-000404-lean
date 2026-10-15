import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S0
import Jsp000404.R1LeavesN7_27S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h745 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h746 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h748 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h750 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h752 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 3 5 (by decide) (by decide) with h1246 | h1246
  · linarith only [h1246, h4, h743, h752, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1248 | h1248
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1249 | h1249
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1250 | h1250
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1251 | h1251
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1252 | h1252
            · rcases h0bigk with h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [hlam, p1253_0]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                rcases p1253_3 (m.d 0 1) (by simp) with h1255 | h1255
                · rcases p1253_3 (m.d 0 2) (by simp) with h1256 | h1256
                  · linarith only [h0, h1256, hlam]
                  · rcases p1253_3 (m.d 0 3) (by simp) with h1258 | h1258
                    · linarith only [h1, h1258, hlam]
                    · linarith only [h1258, h4, hlam]
                · linarith only [h0, h1255, hlam]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h1246, h1252, h743, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1253_1, u3ehi1]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h1246, h1252, h743, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1253_1, u3ehi1]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h1246, h744, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1253_1, u3ehi1]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h0, hlam, p1253_0]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [hlam, p1253_0]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h4, hlam, p1253_0]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h600, hlam, p1253_1]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h713, hlam, p1253_0]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h1, hlam, p1253_1]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                rcases p1253_3 (m.d 0 1) (by simp) with h1271 | h1271
                · rcases p1253_3 (m.d 0 2) (by simp) with h1272 | h1272
                  · linarith only [h1272, h4, hlam]
                  · rcases p1253_3 (m.d 0 3) (by simp) with h1274 | h1274
                    · rcases p1253_3 (m.d 0 4) (by simp) with h1275 | h1275
                      · linarith only [h1275, h743, hlam]
                      · linarith only [h1275, h600, hlam]
                    · linarith only [h1274, h4, hlam]
                · linarith only [h0, h1271, hlam]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [hlam, p1253_0]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h1246, h1252, h743, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1253_1, u3ehi1]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h1246, h4, h744, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1253_1, u3ehi1]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h2, hlam, p1253_0]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                rcases p1253_3 (m.d 0 1) (by simp) with h1284 | h1284
                · rcases p1253_3 (m.d 0 2) (by simp) with h1285 | h1285
                  · linarith only [h1285, h600, hlam]
                  · rcases p1253_3 (m.d 0 3) (by simp) with h1287 | h1287
                    · rcases p1253_3 (m.d 0 4) (by simp) with h1288 | h1288
                      · rcases p1253_3 (m.d 0 5) (by simp) with h1289 | h1289
                        · linarith only [h1289, h745, hlam]
                        · linarith only [h1289, h713, hlam]
                      · linarith only [h1288, h600, hlam]
                    · linarith only [h1287, h4, hlam]
                · linarith only [h0, h1284, hlam]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h743, hlam, p1253_0]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [hlam, p1253_0]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h1246, h744, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1253_1, u3ehi1]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h3, hlam, p1253_0]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                rcases p1253_3 (m.d 0 1) (by simp) with h1299 | h1299
                · rcases p1253_3 (m.d 0 2) (by simp) with h1300 | h1300
                  · linarith only [h1300, h713, hlam]
                  · rcases p1253_3 (m.d 0 3) (by simp) with h1302 | h1302
                    · rcases p1253_3 (m.d 0 4) (by simp) with h1303 | h1303
                      · rcases p1253_3 (m.d 0 5) (by simp) with h1304 | h1304
                        · rcases h0emin with h1305 | h1305 | h1305 | h1305 | h1305
                          · rcases h2bigk with h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1253_1, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h4, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h600, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h713, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h0, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h746, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h748, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h750, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              rcases p1306_3 (m.d 0 2) (by simp) with h1317 | h1317
                              · linarith only [h1317, hlam, p1306_0]
                              · rcases p1306_3 (m.d 1 2) (by simp) with h1319 | h1319
                                · linarith only [h1319, h746, hlam]
                                · rcases p1306_3 (m.d 2 3) (by simp) with h1321 | h1321
                                  · rcases p1306_3 (m.d 2 4) (by simp) with h1322 | h1322
                                    · linarith only [h1249, h1322, hlam]
                                    · linarith only [h1322, h600, hlam]
                                  · linarith only [h1321, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              rcases p1306_3 (m.d 0 2) (by simp) with h1326 | h1326
                              · linarith only [h1326, h4, hlam]
                              · linarith only [h0, h1326, hlam]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1251, h713, hc02, hc23, hlam, hphi, p1253_1, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h0, h713, hc12, hc23, hlam, hphi, p1253_1, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              rcases p1306_3 (m.d 0 2) (by simp) with h1332 | h1332
                              · linarith only [h1332, hlam, p1306_0]
                              · rcases p1306_3 (m.d 1 2) (by simp) with h1334 | h1334
                                · linarith only [h1334, h748, hlam]
                                · rcases p1306_3 (m.d 2 3) (by simp) with h1336 | h1336
                                  · rcases p1306_3 (m.d 2 4) (by simp) with h1337 | h1337
                                    · rcases p1306_3 (m.d 2 5) (by simp) with h1338 | h1338
                                      · linarith only [h1251, h1338, hlam]
                                      · linarith only [h1338, h713, hlam]
                                    · linarith only [h1337, hlam, p1306_0]
                                  · linarith only [h1336, h4, hlam]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              rcases p1306_3 (m.d 0 2) (by simp) with h1343 | h1343
                              · linarith only [h1343, h600, hlam]
                              · linarith only [h0, h1343, hlam]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1249, hlam, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h0, h713, hc12, hc24, hlam, hphi, p1253_1, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              rcases p1306_3 (m.d 0 2) (by simp) with h1349 | h1349
                              · linarith only [h1349, hlam, p1306_0]
                              · rcases p1306_3 (m.d 1 2) (by simp) with h1351 | h1351
                                · linarith only [h1351, h750, hlam]
                                · rcases p1306_3 (m.d 2 3) (by simp) with h1353 | h1353
                                  · rcases p1306_3 (m.d 2 4) (by simp) with h1354 | h1354
                                    · rcases p1306_3 (m.d 2 5) (by simp) with h1355 | h1355
                                      · rcases h5bigk with h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c | h1356c
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          rcases p1356_3 (m.d 0 5) (by simp) with h1358 | h1358
                                          · rcases p1356_3 (m.d 1 5) (by simp) with h1359 | h1359
                                            · linarith only [h1359, h3, hlam]
                                            · rcases p1356_3 (m.d 2 5) (by simp) with h1361 | h1361
                                              · rcases p1356_3 (m.d 3 5) (by simp) with h1362 | h1362
                                                · linarith only [h1362, h744, hlam]
                                                · linarith only [h1246, h1362, hlam]
                                              · linarith only [h1361, h750, hlam]
                                          · linarith only [h1358, h3, hlam]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h713, hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h1246, h4, h743, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1356_1, u3ehi1]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          rcases p1356_3 (m.d 0 5) (by simp) with h1369 | h1369
                                          · rcases p1356_3 (m.d 1 5) (by simp) with h1370 | h1370
                                            · linarith only [h1370, h3, hlam]
                                            · linarith only [h1248, h1370, hlam]
                                          · linarith only [h1369, h745, hlam]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h3, hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h750, hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h1246, hlam, p1356_1]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p1356_1, u5ehi4]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p1253_1, p1356_1]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          rcases p1356_3 (m.d 0 5) (by simp) with h1380 | h1380
                                          · linarith only [h1380, h713, hlam]
                                          · linarith only [h1380, h3, hlam]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h1246, h1249, h1251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1356_1, u3ehi1]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          rcases p1356_3 (m.d 0 5) (by simp) with h1385 | h1385
                                          · linarith only [h1385, h713, hlam]
                                          · linarith only [h1385, h745, hlam]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h744, hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h1252, h4, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1356_1, u5ehi1]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h1250, hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h1252, h4, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1356_1, u5ehi4]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h745, hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h1248, hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h1251, hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [h1252, hlam, p1356_0]
                                        · have p1356_0 := h1356c.1
                                          have p1356_1 := h1356c.2.1
                                          have p1356_2 := h1356c.2.2.1
                                          have p1356_3 := h1356c.2.2.2
                                          linarith only [hlam, p1356_0]
                                      · linarith only [h1355, hlam, p1306_0]
                                    · linarith only [h1354, h600, hlam]
                                  · linarith only [h1353, h4, hlam]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              rcases p1306_3 (m.d 0 2) (by simp) with h1401 | h1401
                              · linarith only [h1401, h713, hlam]
                              · linarith only [h0, h1401, hlam]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1250, hlam, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1251, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hlam, p1306_0]
                          · linarith only [h1305, hc05, hlam, p1253_1]
                          · rcases h2bigk with h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c | h1408c
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h1249, h1251, h713, hc12, hc23, hlam, hphi, p1253_1, p1408_1]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h4, hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h600, hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h713, hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h0, hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h746, hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h748, hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h750, hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              rcases p1408_3 (m.d 0 2) (by simp) with h1419 | h1419
                              · linarith only [h1419, hlam, p1408_0]
                              · rcases p1408_3 (m.d 1 2) (by simp) with h1421 | h1421
                                · linarith only [h1421, h746, hlam]
                                · rcases p1408_3 (m.d 2 3) (by simp) with h1423 | h1423
                                  · rcases p1408_3 (m.d 2 4) (by simp) with h1424 | h1424
                                    · linarith only [h1249, h1424, hlam]
                                    · linarith only [h1424, h600, hlam]
                                  · linarith only [h1423, hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              rcases p1408_3 (m.d 0 2) (by simp) with h1428 | h1428
                              · linarith only [h1428, h4, hlam]
                              · linarith only [h0, h1428, hlam]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h1251, h713, hc02, hc23, hlam, hphi, p1253_1, p1408_1]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h0, h713, hc12, hc23, hlam, hphi, p1253_1, p1408_1]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              rcases p1408_3 (m.d 0 2) (by simp) with h1434 | h1434
                              · linarith only [h1434, hlam, p1408_0]
                              · rcases p1408_3 (m.d 1 2) (by simp) with h1436 | h1436
                                · linarith only [h1436, h748, hlam]
                                · rcases p1408_3 (m.d 2 3) (by simp) with h1438 | h1438
                                  · rcases p1408_3 (m.d 2 4) (by simp) with h1439 | h1439
                                    · rcases p1408_3 (m.d 2 5) (by simp) with h1440 | h1440
                                      · linarith only [h1251, h1440, hlam]
                                      · linarith only [h1440, h713, hlam]
                                    · linarith only [h1439, hlam, p1408_0]
                                  · linarith only [h1438, h4, hlam]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              rcases p1408_3 (m.d 0 2) (by simp) with h1445 | h1445
                              · linarith only [h1445, h600, hlam]
                              · linarith only [h0, h1445, hlam]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h1249, hlam, p1408_1]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h0, h713, hc12, hc24, hlam, hphi, p1253_1, p1408_1]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              rcases p1408_3 (m.d 0 2) (by simp) with h1451 | h1451
                              · linarith only [h1451, hlam, p1408_0]
                              · rcases p1408_3 (m.d 1 2) (by simp) with h1453 | h1453
                                · linarith only [h1453, h750, hlam]
                                · rcases p1408_3 (m.d 2 3) (by simp) with h1455 | h1455
                                  · rcases p1408_3 (m.d 2 4) (by simp) with h1456 | h1456
                                    · rcases p1408_3 (m.d 2 5) (by simp) with h1457 | h1457
                                      · rcases h5bigk with h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c | h1458c
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          rcases p1458_3 (m.d 0 5) (by simp) with h1460 | h1460
                                          · rcases p1458_3 (m.d 1 5) (by simp) with h1461 | h1461
                                            · linarith only [h1461, h3, hlam]
                                            · rcases p1458_3 (m.d 2 5) (by simp) with h1463 | h1463
                                              · rcases p1458_3 (m.d 3 5) (by simp) with h1464 | h1464
                                                · linarith only [h1464, h744, hlam]
                                                · linarith only [h1246, h1464, hlam]
                                              · linarith only [h1463, h750, hlam]
                                          · linarith only [h1460, h3, hlam]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h713, hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h1246, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1458_1, u3ehi1]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          rcases p1458_3 (m.d 0 5) (by simp) with h1471 | h1471
                                          · rcases p1458_3 (m.d 1 5) (by simp) with h1472 | h1472
                                            · linarith only [h1472, h3, hlam]
                                            · linarith only [h1248, h1472, hlam]
                                          · linarith only [h1471, h745, hlam]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h3, hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h750, hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h1246, hlam, p1458_1]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p1458_1, u5ehi4]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h0, h1249, h1251, hc12, hc23, hlam, hphi, p1253_1, p1458_1]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          rcases p1458_3 (m.d 0 5) (by simp) with h1482 | h1482
                                          · linarith only [h1482, h713, hlam]
                                          · linarith only [h1482, h3, hlam]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h1246, h1249, h1251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1458_1, u3ehi1]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          rcases p1458_3 (m.d 0 5) (by simp) with h1487 | h1487
                                          · linarith only [h1487, h713, hlam]
                                          · linarith only [h1487, h745, hlam]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h744, hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h4, h744, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1458_1, u5ehi1]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h1250, hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h1252, h4, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1458_1, u5ehi4]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h745, hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h1248, hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h1251, hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [h1252, hlam, p1458_0]
                                        · have p1458_0 := h1458c.1
                                          have p1458_1 := h1458c.2.1
                                          have p1458_2 := h1458c.2.2.1
                                          have p1458_3 := h1458c.2.2.2
                                          linarith only [hlam, p1458_0]
                                      · linarith only [h1457, hlam, p1408_0]
                                    · linarith only [h1456, h600, hlam]
                                  · linarith only [h1455, h4, hlam]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              rcases p1408_3 (m.d 0 2) (by simp) with h1503 | h1503
                              · linarith only [h1503, h713, hlam]
                              · linarith only [h0, h1503, hlam]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h1250, hlam, p1408_1]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [h1251, hlam, p1408_0]
                            · have p1408_0 := h1408c.1
                              have p1408_1 := h1408c.2.1
                              have p1408_2 := h1408c.2.2.1
                              have p1408_3 := h1408c.2.2.2
                              linarith only [hlam, p1408_0]
                          · rcases h2bigk with h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1253_1, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h4, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h600, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h713, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h0, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h746, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h748, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h750, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              rcases p1509_3 (m.d 0 2) (by simp) with h1520 | h1520
                              · linarith only [h1520, hlam, p1509_0]
                              · rcases p1509_3 (m.d 1 2) (by simp) with h1522 | h1522
                                · linarith only [h1522, h746, hlam]
                                · rcases p1509_3 (m.d 2 3) (by simp) with h1524 | h1524
                                  · rcases p1509_3 (m.d 2 4) (by simp) with h1525 | h1525
                                    · linarith only [h1249, h1525, hlam]
                                    · linarith only [h1525, h600, hlam]
                                  · linarith only [h1524, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              rcases p1509_3 (m.d 0 2) (by simp) with h1529 | h1529
                              · linarith only [h1529, h4, hlam]
                              · linarith only [h0, h1529, hlam]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1251, h713, hc02, hc23, hlam, hphi, p1253_1, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h0, h713, hc12, hc23, hlam, hphi, p1253_1, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              rcases p1509_3 (m.d 0 2) (by simp) with h1535 | h1535
                              · linarith only [h1535, hlam, p1509_0]
                              · rcases p1509_3 (m.d 1 2) (by simp) with h1537 | h1537
                                · linarith only [h1537, h748, hlam]
                                · rcases p1509_3 (m.d 2 3) (by simp) with h1539 | h1539
                                  · rcases p1509_3 (m.d 2 4) (by simp) with h1540 | h1540
                                    · rcases p1509_3 (m.d 2 5) (by simp) with h1541 | h1541
                                      · linarith only [h1251, h1541, hlam]
                                      · linarith only [h1541, h713, hlam]
                                    · linarith only [h1540, hlam, p1509_0]
                                  · linarith only [h1539, h4, hlam]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              rcases p1509_3 (m.d 0 2) (by simp) with h1546 | h1546
                              · linarith only [h1546, h600, hlam]
                              · linarith only [h0, h1546, hlam]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1249, hlam, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h0, h713, hc12, hc24, hlam, hphi, p1253_1, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              rcases p1509_3 (m.d 0 2) (by simp) with h1552 | h1552
                              · linarith only [h1552, hlam, p1509_0]
                              · rcases p1509_3 (m.d 1 2) (by simp) with h1554 | h1554
                                · linarith only [h1554, h750, hlam]
                                · rcases p1509_3 (m.d 2 3) (by simp) with h1556 | h1556
                                  · rcases p1509_3 (m.d 2 4) (by simp) with h1557 | h1557
                                    · rcases p1509_3 (m.d 2 5) (by simp) with h1558 | h1558
                                      · rcases h5bigk with h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c | h1559c
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          rcases p1559_3 (m.d 0 5) (by simp) with h1561 | h1561
                                          · rcases p1559_3 (m.d 1 5) (by simp) with h1562 | h1562
                                            · linarith only [h1562, h3, hlam]
                                            · rcases p1559_3 (m.d 2 5) (by simp) with h1564 | h1564
                                              · rcases p1559_3 (m.d 3 5) (by simp) with h1565 | h1565
                                                · linarith only [h1565, h744, hlam]
                                                · linarith only [h1246, h1565, hlam]
                                              · linarith only [h1564, h750, hlam]
                                          · linarith only [h1561, h3, hlam]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h713, hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h1246, h1249, h600, h745, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1559_1, u3ehi1]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          rcases p1559_3 (m.d 0 5) (by simp) with h1572 | h1572
                                          · rcases p1559_3 (m.d 1 5) (by simp) with h1573 | h1573
                                            · linarith only [h1573, h3, hlam]
                                            · linarith only [h1248, h1573, hlam]
                                          · linarith only [h1572, h745, hlam]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h3, hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h750, hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h1246, hlam, p1559_1]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p1559_1, u5ehi4]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h0, hc12, hc25, hlam, hphi, p1253_1, p1559_1]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          rcases p1559_3 (m.d 0 5) (by simp) with h1583 | h1583
                                          · linarith only [h1583, h713, hlam]
                                          · linarith only [h1583, h3, hlam]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h1246, h1249, h1251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1559_1, u3ehi1]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          rcases p1559_3 (m.d 0 5) (by simp) with h1588 | h1588
                                          · linarith only [h1588, h713, hlam]
                                          · linarith only [h1588, h745, hlam]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h744, hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h1252, h743, hc03, hlam, hphi, ht0b, ht5b, p1559_1, u5ehi1]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h1250, hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h1252, h4, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1559_1, u5ehi4]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h745, hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h1248, hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h1251, hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [h1252, hlam, p1559_0]
                                        · have p1559_0 := h1559c.1
                                          have p1559_1 := h1559c.2.1
                                          have p1559_2 := h1559c.2.2.1
                                          have p1559_3 := h1559c.2.2.2
                                          linarith only [hlam, p1559_0]
                                      · linarith only [h1558, hlam, p1509_0]
                                    · linarith only [h1557, h600, hlam]
                                  · linarith only [h1556, h4, hlam]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              rcases p1509_3 (m.d 0 2) (by simp) with h1604 | h1604
                              · linarith only [h1604, h713, hlam]
                              · linarith only [h0, h1604, hlam]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1250, hlam, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1251, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                          · rcases h2bigk with h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h4, hc12, hc23, hlam, hphi, p1610_1]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h4, hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h600, hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h713, hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h0, hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h746, hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h748, hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h750, hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              rcases p1610_3 (m.d 0 2) (by simp) with h1621 | h1621
                              · linarith only [h1621, hlam, p1610_0]
                              · rcases p1610_3 (m.d 1 2) (by simp) with h1623 | h1623
                                · linarith only [h1623, h746, hlam]
                                · rcases p1610_3 (m.d 2 3) (by simp) with h1625 | h1625
                                  · rcases p1610_3 (m.d 2 4) (by simp) with h1626 | h1626
                                    · linarith only [h1249, h1626, hlam]
                                    · linarith only [h1626, h600, hlam]
                                  · linarith only [h1625, hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              rcases p1610_3 (m.d 0 2) (by simp) with h1630 | h1630
                              · linarith only [h1630, h4, hlam]
                              · linarith only [h0, h1630, hlam]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h600, hc02, hc23, hlam, hphi, p1610_1]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h1305, h713, hc23, hlam, ht01, ht12, p1610_1]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              rcases p1610_3 (m.d 0 2) (by simp) with h1636 | h1636
                              · linarith only [h1636, hlam, p1610_0]
                              · rcases p1610_3 (m.d 1 2) (by simp) with h1638 | h1638
                                · linarith only [h1638, h748, hlam]
                                · rcases p1610_3 (m.d 2 3) (by simp) with h1640 | h1640
                                  · rcases p1610_3 (m.d 2 4) (by simp) with h1641 | h1641
                                    · rcases p1610_3 (m.d 2 5) (by simp) with h1642 | h1642
                                      · linarith only [h1251, h1642, hlam]
                                      · linarith only [h1642, h713, hlam]
                                    · linarith only [h1641, hlam, p1610_0]
                                  · linarith only [h1640, h4, hlam]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              rcases p1610_3 (m.d 0 2) (by simp) with h1647 | h1647
                              · linarith only [h1647, h600, hlam]
                              · linarith only [h0, h1647, hlam]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h1249, hlam, p1610_1]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h1305, h713, hc24, hlam, ht01, ht12, p1610_1]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              rcases p1610_3 (m.d 0 2) (by simp) with h1653 | h1653
                              · linarith only [h1653, hlam, p1610_0]
                              · rcases p1610_3 (m.d 1 2) (by simp) with h1655 | h1655
                                · linarith only [h1655, h750, hlam]
                                · rcases p1610_3 (m.d 2 3) (by simp) with h1657 | h1657
                                  · rcases p1610_3 (m.d 2 4) (by simp) with h1658 | h1658
                                    · rcases p1610_3 (m.d 2 5) (by simp) with h1659 | h1659
                                      · rcases h5bigk with h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          rcases p1660_3 (m.d 0 5) (by simp) with h1662 | h1662
                                          · rcases p1660_3 (m.d 1 5) (by simp) with h1663 | h1663
                                            · linarith only [h1663, h3, hlam]
                                            · rcases p1660_3 (m.d 2 5) (by simp) with h1665 | h1665
                                              · rcases p1660_3 (m.d 3 5) (by simp) with h1666 | h1666
                                                · linarith only [h1666, h744, hlam]
                                                · linarith only [h1246, h1666, hlam]
                                              · linarith only [h1665, h750, hlam]
                                          · linarith only [h1662, h3, hlam]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h713, hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h1246, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1660_1, u3ehi1]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          rcases p1660_3 (m.d 0 5) (by simp) with h1673 | h1673
                                          · rcases p1660_3 (m.d 1 5) (by simp) with h1674 | h1674
                                            · linarith only [h1674, h3, hlam]
                                            · linarith only [h1248, h1674, hlam]
                                          · linarith only [h1673, h745, hlam]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h3, hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h750, hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h1246, hlam, p1660_1]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p1660_1, u5ehi4]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h1249, h1251, h1305, hc23, hlam, ht01, ht12, p1660_1]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          rcases p1660_3 (m.d 0 5) (by simp) with h1684 | h1684
                                          · linarith only [h1684, h713, hlam]
                                          · linarith only [h1684, h3, hlam]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h1246, h1249, h1251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1660_1, u3ehi1]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          rcases p1660_3 (m.d 0 5) (by simp) with h1689 | h1689
                                          · linarith only [h1689, h713, hlam]
                                          · linarith only [h1689, h745, hlam]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h744, hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h4, h744, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1660_1, u5ehi1]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h1250, hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h1252, h4, h743, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1660_1, u5ehi4]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h745, hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h1248, hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h1251, hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [h1252, hlam, p1660_0]
                                        · have p1660_0 := h1660c.1
                                          have p1660_1 := h1660c.2.1
                                          have p1660_2 := h1660c.2.2.1
                                          have p1660_3 := h1660c.2.2.2
                                          linarith only [hlam, p1660_0]
                                      · linarith only [h1659, hlam, p1610_0]
                                    · linarith only [h1658, h600, hlam]
                                  · linarith only [h1657, h4, hlam]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              rcases p1610_3 (m.d 0 2) (by simp) with h1705 | h1705
                              · linarith only [h1705, h713, hlam]
                              · linarith only [h0, h1705, hlam]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h1250, hlam, p1610_1]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [h1251, hlam, p1610_0]
                            · have p1610_0 := h1610c.1
                              have p1610_1 := h1610c.2.1
                              have p1610_2 := h1610c.2.2.1
                              have p1610_3 := h1610c.2.2.2
                              linarith only [hlam, p1610_0]
                        · linarith only [h1304, h713, hlam]
                      · linarith only [h1303, h600, hlam]
                    · linarith only [h1302, h4, hlam]
                · linarith only [h0, h1299, hlam]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h744, hlam, p1253_0]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [h745, hlam, p1253_1]
              · have p1253_0 := h1253c.1
                have p1253_1 := h1253c.2.1
                have p1253_2 := h1253c.2.2.1
                have p1253_3 := h1253c.2.2.2
                linarith only [hlam, p1253_0]
            · linarith only [h1252, h4, h743, h745, h752, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h1248, h1251, h600, h752, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1250, h4, h743, h752, hc35, hlam, hphi, u3ehi1]
      · linarith only [h1249, h4, h743, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1722 | h1722
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1723 | h1723
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1724 | h1724
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1725 | h1725
            · linarith only [h1248, h1725, h4, h743, h752, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h1725, h4, h743, h745, h752, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h1724, h4, h600, h743, h745, hc12, hc23, hlam, hphi]
        · linarith only [h1723, h4, h744, hlam]
      · linarith only [h1722, h4, h744, hc34, hlam, hphi, u3ehi4]

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h745 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h746 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h748 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h750 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 3 4 (by decide) (by decide) with h752 | h752
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744 h745 h746 h748 h750 h752
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744 h745 h746 h748 h750 h752

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h745 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h746 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h748 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 5 (by decide) (by decide) with h750 | h750
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744 h745 h746 h748 h750
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744 h745 h746 h748 h750

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h745 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h746 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 4 (by decide) (by decide) with h748 | h748
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744 h745 h746 h748
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744 h745 h746 h748

set_option maxHeartbeats 5826000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h600 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h713 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h743 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h744 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h745 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 3 (by decide) (by decide) with h746 | h746
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744 h745 h746
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h1 h2 h3 h4 h600 h713 h743 h744 h745 h746

end R2N4
