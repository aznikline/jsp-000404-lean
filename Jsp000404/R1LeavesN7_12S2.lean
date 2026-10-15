import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S0
import Jsp000404.R1LeavesN7_12S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h619 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h696 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h698 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 3 5 (by decide) (by decide) with h1237 | h1237
  · linarith only [h0, h1237, h4, h698, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1239 | h1239
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1240 | h1240
      · linarith only [h0, h1239, h1240, h4, h698, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1242 | h1242
        · linarith only [h0, h1237, h1240, h1242, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1244 | h1244
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1245 | h1245
            · rcases h1bigk with h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h0, h1242, h1245, h4, h7, h9, hlam, p1246_2]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                rcases p1246_3 (m.d 0 1) (by simp) with h1249 | h1249
                · rcases p1246_3 (m.d 1 2) (by simp) with h1250 | h1250
                  · linarith only [h0, h1250, hlam]
                  · rcases p1246_3 (m.d 1 3) (by simp) with h1252 | h1252
                    · linarith only [h1252, hlam, p1246_0]
                    · rcases p1246_3 (m.d 1 4) (by simp) with h1254 | h1254
                      · linarith only [h1254, h2, hlam]
                      · linarith only [h1254, h698, hlam]
                · linarith only [h1249, hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h1239, hc01, hlam, hphi, ht0b, ht5b, p1246_1, u5ehi4]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                rcases p1246_3 (m.d 0 1) (by simp) with h1259 | h1259
                · rcases p1246_3 (m.d 1 2) (by simp) with h1260 | h1260
                  · linarith only [h0, h1260, hlam]
                  · rcases p1246_3 (m.d 1 3) (by simp) with h1262 | h1262
                    · linarith only [h1, h1262, hlam]
                    · rcases p1246_3 (m.d 1 4) (by simp) with h1264 | h1264
                      · linarith only [h1264, h2, hlam]
                      · linarith only [h1239, h1264, hlam]
                · linarith only [h1259, hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h0, hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h9, hlam, p1246_1]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h619, hlam, p1246_1]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h696, hlam, p1246_1]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h1, hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h0, h1242, h1245, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1246_1]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h698, hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h1237, hlam, p1246_1]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h2, hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                rcases p1246_3 (m.d 0 1) (by simp) with h1279 | h1279
                · rcases p1246_3 (m.d 1 2) (by simp) with h1280 | h1280
                  · linarith only [h1280, h619, hlam]
                  · rcases p1246_3 (m.d 1 3) (by simp) with h1282 | h1282
                    · linarith only [h1282, h698, hlam]
                    · linarith only [h1282, h9, hlam]
                · linarith only [h0, h1279, hlam]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                rcases p1246_3 (m.d 0 1) (by simp) with h1286 | h1286
                · rcases p1246_3 (m.d 1 2) (by simp) with h1287 | h1287
                  · linarith only [h1287, h619, hlam]
                  · rcases p1246_3 (m.d 1 3) (by simp) with h1289 | h1289
                    · linarith only [h1289, h698, hlam]
                    · rcases p1246_3 (m.d 1 4) (by simp) with h1291 | h1291
                      · rcases p1246_3 (m.d 1 5) (by simp) with h1292 | h1292
                        · linarith only [h1239, h1292, hlam]
                        · linarith only [h1237, h1292, hlam]
                      · linarith only [h1291, h698, hlam]
                · linarith only [h1, h1286, hlam]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h1239, h2, hc01, hlam, hphi, ht0b, ht5b, p1246_1, u5ehi4]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h3, hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                rcases p1246_3 (m.d 0 1) (by simp) with h1300 | h1300
                · rcases p1246_3 (m.d 1 2) (by simp) with h1301 | h1301
                  · linarith only [h1301, h696, hlam]
                  · rcases p1246_3 (m.d 1 3) (by simp) with h1303 | h1303
                    · linarith only [h1237, h1303, hlam]
                    · linarith only [h1303, h9, hlam]
                · linarith only [h0, h1300, hlam]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                rcases p1246_3 (m.d 0 1) (by simp) with h1307 | h1307
                · rcases p1246_3 (m.d 1 2) (by simp) with h1308 | h1308
                  · linarith only [h1308, h696, hlam]
                  · rcases p1246_3 (m.d 1 3) (by simp) with h1310 | h1310
                    · linarith only [h1237, h1310, hlam]
                    · rcases p1246_3 (m.d 1 4) (by simp) with h1312 | h1312
                      · rcases p1246_3 (m.d 1 5) (by simp) with h1313 | h1313
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
                            linarith only [h1242, h1245, h4, h7, h9, hlam, p1314_2]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            rcases p1314_3 (m.d 0 2) (by simp) with h1317 | h1317
                            · rcases p1314_3 (m.d 1 2) (by simp) with h1318 | h1318
                              · linarith only [h0, h1318, hlam]
                              · rcases p1314_3 (m.d 2 3) (by simp) with h1320 | h1320
                                · linarith only [h1320, hlam, p1314_0]
                                · rcases p1314_3 (m.d 2 4) (by simp) with h1322 | h1322
                                  · linarith only [h1322, h5, hlam]
                                  · linarith only [h1240, h1322, hlam]
                            · linarith only [h1317, hlam, p1314_0]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h0, h1239, h619, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1246_1, p1314_1]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h0, h696, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1246_1, p1314_1]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h0, hlam, p1314_1]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [hlam, p1314_0]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h9, hlam, p1314_0]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h619, hlam, p1314_0]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h696, hlam, p1314_0]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h4, hlam, p1314_0]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h0, h1242, h1245, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1314_1]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [hlam, p1314_0]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h1240, hlam, p1314_1]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h1242, hlam, p1314_1]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h5, hlam, p1314_0]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            rcases p1314_3 (m.d 0 2) (by simp) with h1339 | h1339
                            · rcases p1314_3 (m.d 1 2) (by simp) with h1340 | h1340
                              · linarith only [h1340, hlam, p1314_0]
                              · rcases p1314_3 (m.d 2 3) (by simp) with h1342 | h1342
                                · linarith only [h1240, h1342, hlam]
                                · linarith only [h1342, h9, hlam]
                            · linarith only [h0, h1339, hlam]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h0, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1314_1]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [hlam, p1314_0]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h0, h1240, h4, h696, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1246_1, p1314_1]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h6, hlam, p1314_0]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            rcases p1314_3 (m.d 0 2) (by simp) with h1350 | h1350
                            · rcases p1314_3 (m.d 1 2) (by simp) with h1351 | h1351
                              · linarith only [h1351, hlam, p1314_0]
                              · rcases p1314_3 (m.d 2 3) (by simp) with h1353 | h1353
                                · linarith only [h1242, h1353, hlam]
                                · linarith only [h1353, h9, hlam]
                            · linarith only [h0, h1350, hlam]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h9, hc12, hc25, hlam, hphi, p1314_1]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [h1244, hlam, p1314_1]
                          · have p1314_0 := h1314c.1
                            have p1314_1 := h1314c.2.1
                            have p1314_2 := h1314c.2.2.1
                            have p1314_3 := h1314c.2.2.2
                            linarith only [hlam, p1314_0]
                        · linarith only [h1237, h1313, hlam]
                      · linarith only [h1312, h698, hlam]
                · linarith only [h1, h1307, hlam]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [h1239, hlam, p1246_0]
              · have p1246_0 := h1246c.1
                have p1246_1 := h1246c.2.1
                have p1246_2 := h1246c.2.2.1
                have p1246_3 := h1246c.2.2.2
                linarith only [hlam, p1246_0]
            · linarith only [h1239, h1240, h1245, h619, hlam]
          · linarith only [h1239, h1244, h619, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1367 | h1367
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1368 | h1368
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1369 | h1369
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1370 | h1370
            · linarith only [h0, h1239, h1367, h1370, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1367, h1369, h1370, h4, h698, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1373 | h1373
            · linarith only [h0, h1369, h1373, h4, h619, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h1bigk with h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c | h1375c
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [hlam, p1375_0]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h0, h1367, h1369, h4, h698, h7, h8, h9, hlam, p1375_2]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h0, h1367, h1369, h4, h698, h7, h8, hlam, p1375_2]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                rcases p1375_3 (m.d 0 1) (by simp) with h1379 | h1379
                · rcases p1375_3 (m.d 1 2) (by simp) with h1380 | h1380
                  · linarith only [h0, h1380, hlam]
                  · rcases p1375_3 (m.d 1 3) (by simp) with h1382 | h1382
                    · linarith only [h1, h1382, hlam]
                    · rcases p1375_3 (m.d 1 4) (by simp) with h1384 | h1384
                      · linarith only [h1384, hlam, p1375_0]
                      · rcases p1375_3 (m.d 1 5) (by simp) with h1386 | h1386
                        · linarith only [h1386, h3, hlam]
                        · linarith only [h1239, h1386, hlam]
                · linarith only [h1379, hlam, p1375_0]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                rcases p1375_3 (m.d 0 1) (by simp) with h1390 | h1390
                · rcases p1375_3 (m.d 1 2) (by simp) with h1391 | h1391
                  · linarith only [h0, h1391, hlam]
                  · rcases p1375_3 (m.d 1 3) (by simp) with h1393 | h1393
                    · linarith only [h1, h1393, hlam]
                    · rcases p1375_3 (m.d 1 4) (by simp) with h1395 | h1395
                      · linarith only [h1395, h2, hlam]
                      · rcases p1375_3 (m.d 1 5) (by simp) with h1397 | h1397
                        · linarith only [h1397, hlam, p1375_0]
                        · rcases h2bigk with h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c | h1399c
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1367, h1369, h4, h698, h7, h8, h9, hlam, p1399_2]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h0, h1367, h698, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1399_1]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            rcases p1399_3 (m.d 0 2) (by simp) with h1403 | h1403
                            · rcases p1399_3 (m.d 1 2) (by simp) with h1404 | h1404
                              · linarith only [h0, h1404, hlam]
                              · rcases p1399_3 (m.d 2 3) (by simp) with h1406 | h1406
                                · linarith only [h1406, h4, hlam]
                                · linarith only [h1367, h1406, hlam]
                            · linarith only [h1403, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            rcases p1399_3 (m.d 0 2) (by simp) with h1410 | h1410
                            · rcases p1399_3 (m.d 1 2) (by simp) with h1411 | h1411
                              · linarith only [h0, h1411, hlam]
                              · rcases p1399_3 (m.d 2 3) (by simp) with h1413 | h1413
                                · linarith only [h1413, h4, hlam]
                                · linarith only [h1368, h1413, hlam]
                            · linarith only [h1410, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h0, hlam, p1399_1]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h9, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h619, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h696, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h4, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            rcases p1399_3 (m.d 0 2) (by simp) with h1423 | h1423
                            · rcases p1399_3 (m.d 1 2) (by simp) with h1424 | h1424
                              · linarith only [h1424, hlam, p1399_0]
                              · rcases p1399_3 (m.d 2 3) (by simp) with h1426 | h1426
                                · rcases p1399_3 (m.d 2 4) (by simp) with h1427 | h1427
                                  · linarith only [h1367, h1427, hlam]
                                  · linarith only [h1427, h619, hlam]
                                · linarith only [h1426, hlam, p1399_0]
                            · linarith only [h0, h1423, hlam]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1367, h698, h9, hc12, hc23, hlam, hphi, p1399_1]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p1399_1, u5ehi2]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h5, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1369, h7, h8, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1399_1]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1367, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1369, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h6, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            rcases p1399_3 (m.d 0 2) (by simp) with h1441 | h1441
                            · rcases p1399_3 (m.d 1 2) (by simp) with h1442 | h1442
                              · linarith only [h1442, hlam, p1399_0]
                              · rcases p1399_3 (m.d 2 3) (by simp) with h1444 | h1444
                                · rcases p1399_3 (m.d 2 4) (by simp) with h1445 | h1445
                                  · linarith only [h1369, h1445, hlam]
                                  · linarith only [h1445, h619, hlam]
                                · linarith only [h1444, h9, hlam]
                            · linarith only [h0, h1441, hlam]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h1368, hlam, p1399_0]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [h0, h6, h619, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1399_1]
                          · have p1399_0 := h1399c.1
                            have p1399_1 := h1399c.2.1
                            have p1399_2 := h1399c.2.2.1
                            have p1399_3 := h1399c.2.2.2
                            linarith only [hlam, p1399_0]
                · linarith only [h1390, hlam, p1375_0]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h0, hlam, p1375_0]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [hlam, p1375_0]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h9, hlam, p1375_1]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h619, hlam, p1375_1]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h696, hlam, p1375_1]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h1, hlam, p1375_0]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h698, hc12, hc34, hlam, hphi, ht23, p1375_1]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [hlam, p1375_0]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h698, hlam, p1375_0]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h1237, hlam, p1375_1]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h2, hlam, p1375_0]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h0, h1239, h4, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1375_1]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h0, h1239, h4, h7, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1375_1]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [hlam, p1375_0]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h1239, hlam, p1375_1]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h3, hlam, p1375_0]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h0, h1237, h1368, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1375_1]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h0, h1237, h1368, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1375_1]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [h0, h1237, h1368, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1375_1]
              · have p1375_0 := h1375c.1
                have p1375_1 := h1375c.2.1
                have p1375_2 := h1375c.2.2.1
                have p1375_3 := h1375c.2.2.2
                linarith only [hlam, p1375_0]
        · linarith only [h1367, h1368, h698, h9, hc12, hc35, hlam, hphi, ht23]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1475 | h1475
        · linarith only [h0, h1367, h1475, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1477 | h1477
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1478 | h1478
            · rcases h1bigk with h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c | h1479c
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [hlam, p1479_0]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h0, h1475, h1478, h4, h7, h9, hlam, p1479_2]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h0, h1239, h1367, h1477, h4, h698, h7, hlam, p1479_2]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h0, h1239, h1367, h1477, h4, h7, hlam, p1479_2]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                rcases p1479_3 (m.d 0 1) (by simp) with h1484 | h1484
                · rcases p1479_3 (m.d 1 2) (by simp) with h1485 | h1485
                  · linarith only [h0, h1485, hlam]
                  · rcases p1479_3 (m.d 1 3) (by simp) with h1487 | h1487
                    · linarith only [h1, h1487, hlam]
                    · rcases p1479_3 (m.d 1 4) (by simp) with h1489 | h1489
                      · linarith only [h1489, h2, hlam]
                      · rcases p1479_3 (m.d 1 5) (by simp) with h1491 | h1491
                        · linarith only [h1491, hlam, p1479_0]
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
                            linarith only [h1239, h1367, h1477, h4, h698, h7, h9, hlam, p1493_2]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            rcases p1493_3 (m.d 0 2) (by simp) with h1496 | h1496
                            · rcases p1493_3 (m.d 1 2) (by simp) with h1497 | h1497
                              · linarith only [h0, h1497, hlam]
                              · rcases p1493_3 (m.d 2 3) (by simp) with h1499 | h1499
                                · linarith only [h1499, hlam, p1493_0]
                                · rcases p1493_3 (m.d 2 4) (by simp) with h1501 | h1501
                                  · linarith only [h1501, h5, hlam]
                                  · linarith only [h1367, h1501, hlam]
                            · linarith only [h1496, hlam, p1493_0]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h0, h1239, h1477, h698, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1493_1]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            rcases p1493_3 (m.d 0 2) (by simp) with h1506 | h1506
                            · rcases p1493_3 (m.d 1 2) (by simp) with h1507 | h1507
                              · linarith only [h0, h1507, hlam]
                              · rcases p1493_3 (m.d 2 3) (by simp) with h1509 | h1509
                                · linarith only [h1509, h4, hlam]
                                · rcases p1493_3 (m.d 2 4) (by simp) with h1511 | h1511
                                  · linarith only [h1511, h5, hlam]
                                  · linarith only [h1477, h1511, hlam]
                            · linarith only [h1506, hlam, p1493_0]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h0, hlam, p1493_1]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [hlam, p1493_0]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h9, hlam, p1493_0]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h619, hlam, p1493_0]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h696, hlam, p1493_0]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h4, hlam, p1493_0]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h1475, h1478, hc12, hc34, hlam, hphi, ht23, p1493_1]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [hlam, p1493_0]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h1367, hlam, p1493_1]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h1475, hlam, p1493_1]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h5, hlam, p1493_0]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            rcases p1493_3 (m.d 0 2) (by simp) with h1526 | h1526
                            · rcases p1493_3 (m.d 1 2) (by simp) with h1527 | h1527
                              · linarith only [h1527, hlam, p1493_0]
                              · rcases p1493_3 (m.d 2 3) (by simp) with h1529 | h1529
                                · linarith only [h1367, h1529, hlam]
                                · linarith only [h1529, h9, hlam]
                            · linarith only [h0, h1526, hlam]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h9, hc12, hc24, hlam, hphi, p1493_1]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [hlam, p1493_0]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h0, h1367, h4, h7, hc01, hlam, hphi, ht0b, ht5b, p1493_1, u5ehi2]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h6, hlam, p1493_0]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            rcases p1493_3 (m.d 0 2) (by simp) with h1537 | h1537
                            · rcases p1493_3 (m.d 1 2) (by simp) with h1538 | h1538
                              · linarith only [h1538, hlam, p1493_0]
                              · rcases p1493_3 (m.d 2 3) (by simp) with h1540 | h1540
                                · linarith only [h1475, h1540, hlam]
                                · linarith only [h1540, h9, hlam]
                            · linarith only [h0, h1537, hlam]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h9, hc12, hc25, hlam, hphi, p1493_1]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [h1477, hlam, p1493_1]
                          · have p1493_0 := h1493c.1
                            have p1493_1 := h1493c.2.1
                            have p1493_2 := h1493c.2.2.1
                            have p1493_3 := h1493c.2.2.2
                            linarith only [hlam, p1493_0]
                · linarith only [h1484, hlam, p1479_0]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h0, hlam, p1479_0]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [hlam, p1479_0]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h9, hlam, p1479_1]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h619, hlam, p1479_1]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h696, hlam, p1479_1]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h1, hlam, p1479_0]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h1239, h698, hc12, hc45, hlam, hphi, ht23, ht34, p1479_1]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [hlam, p1479_0]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h698, hlam, p1479_0]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h1237, hlam, p1479_1]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h2, hlam, p1479_0]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h0, h1239, h4, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1479_1]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h0, h1239, h4, h7, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1479_1]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [hlam, p1479_0]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h1239, hlam, p1479_1]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h3, hlam, p1479_0]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h0, h1239, h1367, h1477, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1479_1]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h0, h1239, h1367, h1477, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1479_1]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [h0, h1239, h1367, h1477, h4, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1479_1]
              · have p1479_0 := h1479c.1
                have p1479_1 := h1479c.2.1
                have p1479_2 := h1479c.2.2.1
                have p1479_3 := h1479c.2.2.2
                linarith only [hlam, p1479_0]
            · linarith only [h1367, h1477, h1478, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1569 | h1569
            · linarith only [h0, h1367, h1477, h1569, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h1367, h1569, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h619 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h696 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 3 4 (by decide) (by decide) with h698 | h698
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h619 h696 h698
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h619 h696 h698

set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h619 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 5 (by decide) (by decide) with h696 | h696
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h619 h696
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h619 h696

set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 4 (by decide) (by decide) with h619 | h619
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h619
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9 h619

set_option maxHeartbeats 6742000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9

end R2N4
