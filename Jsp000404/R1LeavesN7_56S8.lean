import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_56S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4024000 in
set_option maxHeartbeats 4024000 in
theorem r1l7_14_25_L_0_H_I_x1_x1 (m : N7Model)
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1103 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1338 | h1338
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1339 | h1339
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1340 | h1340
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1341 | h1341
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1342 | h1342
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1343 | h1343
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1344 | h1344
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1345 | h1345
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1346 | h1346
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1347 | h1347
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1348 | h1348
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1349 | h1349
                        · rcases h5bigk with h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c | h1350c
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [hlam, p1350_0]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1103, hlam, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1340, h1347, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1350_1, u4elo0]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h0, h1340, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1350_1, u4elo1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h0, h1340, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1350_1, u4elo1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1103, hc01, hc15, hlam, hphi, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [hlam, p1350_0]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1345, h1347, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1350_1, u4elo1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1345, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1350_1, u4elo1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1350_1, u4elo1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1338, hlam, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1342, hlam, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [hlam, p1350_0]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1338, hc02, hc35, hlam, hphi, ht0b, ht5b, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1103, h1338, h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1350_1, u4elo1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1339, hlam, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1344, hlam, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1347, hlam, p1350_0]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [hlam, p1350_0]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1339, hc03, hc45, hlam, hphi, ht0b, ht5b, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1340, hlam, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1345, hlam, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1348, hlam, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [h1349, hlam, p1350_1]
                          · have p1350_0 := h1350c.1
                            have p1350_1 := h1350c.2.1
                            have p1350_2 := h1350c.2.2.1
                            have p1350_3 := h1350c.2.2.2
                            linarith only [hlam, p1350_0]
                        · linarith only [h0, h1340, h1349, hc34, hlam, hphi, u4elo1]
                      · linarith only [h0, h1340, h1348, hc24, hlam, hphi, u4elo1]
                    · linarith only [h1103, h1339, h1345, h1346, h1347, hc34, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1379 | h1379
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1380 | h1380
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1381 | h1381
                        · rcases h5bigk with h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c | h1382c
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [hlam, p1382_0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1103, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1103, h1345, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1382_1, u4elo1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1103, h1345, h1381, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1382_1, u4elo1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1103, h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1382_1, u4elo1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1345, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1382_1, u4elo1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [hlam, p1382_0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1345, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1382_1, u4elo1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1345, h1381, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1382_1, u4elo1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1382_1, u4elo1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1338, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1342, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [hlam, p1382_0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1338, h1381, hc02, hc45, hlam, hphi, ht0b, ht5b, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1103, h1338, h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1382_1, u4elo1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1339, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1344, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1379, hlam, p1382_0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [hlam, p1382_0]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1379, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1340, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1345, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1380, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [h1381, hlam, p1382_1]
                          · have p1382_0 := h1382c.1
                            have p1382_1 := h1382c.2.1
                            have p1382_2 := h1382c.2.2.1
                            have p1382_3 := h1382c.2.2.2
                            linarith only [hlam, p1382_0]
                        · linarith only [h1346, h1381, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1340, h1380, hc24, hlam, hphi, u4elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1410 | h1410
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1411 | h1411
                        · rcases h5bigk with h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [hlam, p1412_0]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1103, hlam, p1412_1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1103, h1345, h1379, hc23, hlam, hphi, ht34, p1412_1, u4elo1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1103, h1345, h1379, hc23, hlam, hphi, ht34, p1412_1, u4elo1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1103, h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1412_1, u4elo1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1345, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1412_1, u4elo1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [hlam, p1412_0]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1345, h1379, hc23, hlam, hphi, ht34, p1412_1, u4elo1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1345, h1379, hc23, hlam, hphi, ht34, p1412_1, u4elo1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1412_1, u4elo1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1338, hlam, p1412_1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1342, hlam, p1412_1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [hlam, p1412_0]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1379, hlam, p1412_1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1338, hc02, hc45, hlam, hphi, ht0b, ht5b, p1412_1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1339, hlam, p1412_1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1344, hlam, p1412_1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1103, h1339, h1345, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1412_1, u4elo1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [hlam, p1412_0]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1103, h1339, h1345, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1412_1, u4elo1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1340, hlam, p1412_1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1345, hlam, p1412_1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1410, hlam, p1412_1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [h1411, hlam, p1412_1]
                          · have p1412_0 := h1412c.1
                            have p1412_1 := h1412c.2.1
                            have p1412_2 := h1412c.2.2.1
                            have p1412_3 := h1412c.2.2.2
                            linarith only [hlam, p1412_0]
                        · linarith only [h0, h1340, h1346, h1411, hc24, hlam, hphi, u4elo1]
                      · linarith only [h0, h1340, h1346, h1410, hc23, hlam, hphi, ht34, u4elo1]
                · linarith only [h0, h1340, h1345, hlam]
              · linarith only [h0, h1339, h1340, h1343, h1344, hc34, hlam, hphi, u4elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1442 | h1442
              · linarith only [h1103, h1343, h1442, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h1103, h1339, h1442, hlam]
          · linarith only [h1338, h1340, h1341, h1342, hc23, hlam, hphi, ht34, u4elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1446 | h1446
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1447 | h1447
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1448 | h1448
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1449 | h1449
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1450 | h1450
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1451 | h1451
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1452 | h1452
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1453 | h1453
                        · rcases h5bigk with h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [hlam, p1454_0]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1103, hlam, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h0, h1340, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1454_1, u4elo1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h0, h1340, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1454_1, u4elo1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h0, h1340, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1454_1, u4elo1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1341, h1446, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [hlam, p1454_0]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1341, h1446, h1451, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1341, h1446, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1449, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1454_1, u4elo1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1338, hlam, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1446, hlam, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [hlam, p1454_0]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1338, hc02, hc35, hlam, hphi, ht0b, ht5b, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1341, h1446, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1339, hlam, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1448, hlam, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1451, hlam, p1454_0]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [hlam, p1454_0]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1339, hc03, hc45, hlam, hphi, ht0b, ht5b, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1340, hlam, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1449, hlam, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1452, hlam, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [h1453, hlam, p1454_1]
                          · have p1454_0 := h1454c.1
                            have p1454_1 := h1454c.2.1
                            have p1454_2 := h1454c.2.2.1
                            have p1454_3 := h1454c.2.2.2
                            linarith only [hlam, p1454_0]
                        · linarith only [h1340, h1453, hc34, hlam, hphi, u4elo0]
                      · linarith only [h0, h1340, h1452, hc24, hlam, hphi, u4elo1]
                    · linarith only [h1339, h1341, h1446, h1451, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1341, h1450, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h0, h1449, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · linarith only [h1103, h1339, h1341, h1446, h1448, hlam]
            · linarith only [h1103, h1341, h1446, h1447, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · linarith only [h1103, h1338, h1446, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1488 | h1488
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1489 | h1489
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1490 | h1490
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1491 | h1491
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1492 | h1492
                · linarith only [h1340, h1492, hc04, hlam, hphi, u4elo1]
                · linarith only [h0, h1492, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · linarith only [h1339, h1340, h1490, h1491, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1496 | h1496
              · linarith only [h1103, h1490, h1496, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h1103, h1339, h1496, hlam]
          · linarith only [h1338, h1340, h1488, h1489, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1500 | h1500
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1501 | h1501
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1502 | h1502
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1503 | h1503
                · linarith only [h0, h1340, h1503, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h1503, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · linarith only [h1103, h1339, h1488, h1500, h1502, hlam]
            · linarith only [h1103, h1488, h1500, h1501, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · linarith only [h1103, h1338, h1500, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1509 | h1509
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1510 | h1510
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1511 | h1511
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1512 | h1512
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1513 | h1513
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1514 | h1514
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1515 | h1515
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1516 | h1516
                    · linarith only [h1338, h1339, h1516, hlam]
                    · linarith only [h1513, h1514, h1515, h1516, hc34, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1519 | h1519
                    · linarith only [h1339, h1515, h1519, hc03, hc34, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1521 | h1521
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1522 | h1522
                        · rcases h5bigk with h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [hlam, p1523_0]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1103, hlam, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1339, h1512, h1522, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1339, hlam, p1523_0]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1339, h1522, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1523_1, u4elo3]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1514, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1523_1, u4elo1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [hlam, p1523_0]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1514, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1523_1, u4elo1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1514, h1519, hc23, hlam, hphi, ht34, p1523_1, u4elo1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1514, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1523_1, u4elo1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1338, hlam, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1511, hlam, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [hlam, p1523_0]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1519, hlam, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1338, hc02, hc45, hlam, hphi, ht0b, ht5b, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1103, hc01, hc35, hlam, hphi, ht12, ht23, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1513, hlam, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1513, h1514, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1523_1, u4elo1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [hlam, p1523_0]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1513, h1514, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1523_1, u4elo1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1509, hlam, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1514, hlam, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1521, hlam, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [h1522, hlam, p1523_1]
                          · have p1523_0 := h1523c.1
                            have p1523_1 := h1523c.2.1
                            have p1523_2 := h1523c.2.2.1
                            have p1523_3 := h1523c.2.2.2
                            linarith only [hlam, p1523_0]
                        · linarith only [h0, h1509, h1515, h1522, hc24, hlam, hphi, u4elo1]
                      · linarith only [h0, h1509, h1515, h1521, hc23, hlam, hphi, ht34, u4elo1]
                · linarith only [h0, h1509, h1514, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1552 | h1552
                · linarith only [h1512, h1513, h1552, hlam]
                · linarith only [h0, h1509, h1552, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1555 | h1555
              · linarith only [h1339, h1512, h1555, hc03, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1557 | h1557
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1558 | h1558
                  · linarith only [h1510, h1512, h1558, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1560 | h1560
                    · linarith only [h1103, h1510, h1555, h1560, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1562 | h1562
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1563 | h1563
                        · rcases h5bigk with h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c | h1564c
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [hlam, p1564_0]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1103, hlam, p1564_1]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1339, h1560, h1563, hc23, hlam, hphi, ht34, p1564_1, u4elo3]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1339, hlam, p1564_0]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1509, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1564_1, u4elo0]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1103, hc01, hc15, hlam, hphi, p1564_1]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [hlam, p1564_0]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1555, h1560, h1563, hc23, hlam, hphi, ht34, p1564_1, u4elo3]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1555, hlam, p1564_0]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1555, h1563, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1564_1, u4elo3]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1338, hlam, p1564_1]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1511, hlam, p1564_1]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [hlam, p1564_0]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1560, hlam, p1564_1]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1338, hc02, hc45, hlam, hphi, ht0b, ht5b, p1564_1]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1103, h1563, hc01, hlam, hphi, ht12, ht23, ht34, p1564_1, u4elo3]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1563, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1564_1, u4elo3]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1563, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1564_1, u4elo3]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [hlam, p1564_0]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1563, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1564_1, u4elo3]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1509, hlam, p1564_1]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1557, hlam, p1564_1]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1562, hlam, p1564_1]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [h1563, hlam, p1564_1]
                          · have p1564_0 := h1564c.1
                            have p1564_1 := h1564c.2.1
                            have p1564_2 := h1564c.2.2.1
                            have p1564_3 := h1564c.2.2.2
                            linarith only [hlam, p1564_0]
                        · linarith only [h0, h1512, h1562, h1563, hc04, hlam, hphi, u4elo2]
                      · linarith only [h1509, h1562, hc24, hlam, hphi, u4elo0]
                · linarith only [h1509, h1557, hc14, hlam, hphi, u4elo0]
          · linarith only [h0, h1338, h1509, h1510, h1511, hc23, hlam, hphi, ht34, u4elo1]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1594 | h1594
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1595 | h1595
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1596 | h1596
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1597 | h1597
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1598 | h1598
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1599 | h1599
                    · linarith only [h1338, h1339, h1599, hlam]
                    · linarith only [h1510, h1596, h1599, hlam]
                  · linarith only [h1103, h1510, h1594, h1598, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h0, h1509, h1597, hlam]
              · linarith only [h1510, h1594, h1596, hlam]
            · linarith only [h1103, h1510, h1594, h1595, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · linarith only [h1103, h1338, h1594, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1607 | h1607
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1608 | h1608
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1609 | h1609
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1610 | h1610
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1611 | h1611
                · linarith only [h1509, h1611, hc04, hlam, hphi, u4elo1]
                · linarith only [h0, h1611, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1614 | h1614
                · linarith only [h0, h1509, h1609, h1610, h1614, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h1614, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1617 | h1617
              · linarith only [h1339, h1609, h1617, hc03, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1619 | h1619
                · linarith only [h0, h1509, h1619, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h1619, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
          · linarith only [h1338, h1509, h1607, h1608, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1623 | h1623
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1624 | h1624
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1625 | h1625
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1626 | h1626
                · linarith only [h0, h1509, h1626, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h1626, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · linarith only [h1607, h1623, h1625, hlam]
            · linarith only [h1103, h1607, h1623, h1624, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · linarith only [h1103, h1338, h1623, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1632 | h1632
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1633 | h1633
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1634 | h1634
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1635 | h1635
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1636 | h1636
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1637 | h1637
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1638 | h1638
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1639 | h1639
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1640 | h1640
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1641 | h1641
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1642 | h1642
                        · rcases h5bigk with h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c | h1643c
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [hlam, p1643_0]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1103, hlam, p1643_1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1338, hlam, p1643_0]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1633, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1643_1, u4elo0]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1103, h1638, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1643_1, u4elo1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1638, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1643_1, u4elo1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [hlam, p1643_0]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1638, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1643_1, u4elo1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1638, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1643_1, u4elo1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1638, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1643_1, u4elo1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1103, hc01, hc25, hlam, hphi, ht12, p1643_1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1635, hlam, p1643_1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [hlam, p1643_0]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1634, h1640, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1643_1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1635, h1638, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1643_1, u4elo1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1632, hlam, p1643_1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1637, hlam, p1643_1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1640, hlam, p1643_0]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [hlam, p1643_0]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1632, hc03, hc45, hlam, hphi, ht0b, ht5b, p1643_1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1633, hlam, p1643_1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1638, hlam, p1643_1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1641, hlam, p1643_1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [h1642, hlam, p1643_1]
                          · have p1643_0 := h1643c.1
                            have p1643_1 := h1643c.2.1
                            have p1643_2 := h1643c.2.2.1
                            have p1643_3 := h1643c.2.2.2
                            linarith only [hlam, p1643_0]
                        · linarith only [h0, h1633, h1642, hc34, hlam, hphi, u4elo1]
                      · linarith only [h0, h1633, h1641, hc24, hlam, hphi, u4elo1]
                    · linarith only [h1103, h1632, h1638, h1639, h1640, hc34, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1672 | h1672
                    · linarith only [h1338, h1639, h1672, hc02, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h1338, h1632, h1672, hlam]
                · linarith only [h0, h1633, h1638, hlam]
              · linarith only [h0, h1632, h1633, h1636, h1637, hc34, hlam, hphi, u4elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1677 | h1677
              · linarith only [h1103, h1636, h1677, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h1338, h1632, h1635, h1677, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1680 | h1680
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1681 | h1681
              · linarith only [h1634, h1635, h1681, hlam]
              · linarith only [h0, h1632, h1633, h1680, h1681, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1684 | h1684
              · linarith only [h1103, h1680, h1684, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h1103, h1632, h1684, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1687 | h1687
          · linarith only [h1338, h1634, h1687, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1689 | h1689
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1690 | h1690
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1691 | h1691
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1692 | h1692
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1693 | h1693
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1694 | h1694
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1695 | h1695
                        · rcases h5bigk with h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c | h1696c
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [hlam, p1696_0]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1103, hlam, p1696_1]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1338, hlam, p1696_0]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1103, h1687, h1694, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1696_1, u4elo2]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1103, h1687, h1694, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1696_1, u4elo2]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1687, h1694, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1696_1, u4elo2]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [hlam, p1696_0]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1687, hlam, p1696_0]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1687, h1694, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1696_1, u4elo2]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1687, h1694, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1696_1, u4elo2]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1103, h1694, hc01, hlam, hphi, ht12, ht23, ht34, p1696_1, u4elo2]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1694, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1696_1, u4elo2]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [hlam, p1696_0]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1694, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1696_1, u4elo2]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1694, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1696_1, u4elo2]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1632, hlam, p1696_1]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1690, hlam, p1696_1]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1693, hlam, p1696_0]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [hlam, p1696_0]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1632, hc03, hc45, hlam, hphi, ht0b, ht5b, p1696_1]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1633, hlam, p1696_1]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1691, hlam, p1696_1]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1694, hlam, p1696_1]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [h1695, hlam, p1696_1]
                          · have p1696_0 := h1696c.1
                            have p1696_1 := h1696c.2.1
                            have p1696_2 := h1696c.2.2.1
                            have p1696_3 := h1696c.2.2.2
                            linarith only [hlam, p1696_0]
                        · linarith only [h0, h1633, h1695, hc34, hlam, hphi, u4elo1]
                      · linarith only [h0, h1633, h1694, hc24, hlam, hphi, u4elo1]
                    · linarith only [h0, h1632, h1633, h1634, h1693, hc12, hlam, hphi, ht23, ht34, u4elo1]
                  · linarith only [h1634, h1692, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h0, h1633, h1691, hlam]
              · linarith only [h0, h1632, h1633, h1689, h1690, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1728 | h1728
              · linarith only [h1103, h1689, h1728, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h1103, h1632, h1728, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1731 | h1731
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1732 | h1732
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1733 | h1733
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1734 | h1734
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1735 | h1735
                · linarith only [h1633, h1735, hc04, hlam, hphi, u4elo1]
                · linarith only [h0, h1735, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · linarith only [h1632, h1633, h1733, h1734, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1739 | h1739
              · linarith only [h1103, h1733, h1739, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h1338, h1632, h1732, h1739, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1742 | h1742
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1743 | h1743
              · linarith only [h1731, h1732, h1743, hlam]
              · linarith only [h0, h1632, h1633, h1742, h1743, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1746 | h1746
              · linarith only [h1103, h1742, h1746, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h1103, h1632, h1746, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1749 | h1749
          · linarith only [h1338, h1731, h1749, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1751 | h1751
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1752 | h1752
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1753 | h1753
                · linarith only [h0, h1633, h1753, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h1753, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · linarith only [h1632, h1633, h1751, h1752, hc34, hlam, hphi, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1757 | h1757
              · linarith only [h1103, h1751, h1757, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h1103, h1632, h1757, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1760 | h1760
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1761 | h1761
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1762 | h1762
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1763 | h1763
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1764 | h1764
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1765 | h1765
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1766 | h1766
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1767 | h1767
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1768 | h1768
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1769 | h1769
                        · rcases h5bigk with h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c | h1770c
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [hlam, p1770_0]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1103, hlam, p1770_1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1338, hlam, p1770_0]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1632, hlam, p1770_0]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1632, h1761, h1766, h1769, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1770_1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1765, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1770_1, u4elo1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [hlam, p1770_0]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1632, h1765, h1767, hc03, hlam, hphi, ht34, p1770_1, u4elo1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1632, h1765, hc03, hlam, hphi, ht34, p1770_1, u4elo1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1765, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1770_1, u4elo1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1103, h1768, hc01, hc24, hlam, hphi, ht12, p1770_1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1762, hlam, p1770_1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [hlam, p1770_0]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1632, h1762, h1765, hc03, hlam, hphi, ht34, p1770_1, u4elo1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1762, h1765, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1770_1, u4elo1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1103, hc01, hc35, hlam, hphi, ht12, ht23, p1770_1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1764, hlam, p1770_1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1767, hlam, p1770_0]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [hlam, p1770_0]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1761, h1766, h1769, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1770_1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1760, hlam, p1770_1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1765, hlam, p1770_1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1768, hlam, p1770_1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [h1769, hlam, p1770_1]
                          · have p1770_0 := h1770c.1
                            have p1770_1 := h1770c.2.1
                            have p1770_2 := h1770c.2.2.1
                            have p1770_3 := h1770c.2.2.2
                            linarith only [hlam, p1770_0]
                        · linarith only [h0, h1760, h1769, hc34, hlam, hphi, u4elo1]
                      · linarith only [h0, h1760, h1768, hc24, hlam, hphi, u4elo1]
                    · linarith only [h1764, h1765, h1766, h1767, hc34, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1799 | h1799
                    · linarith only [h1632, h1766, h1799, hc03, hc34, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1801 | h1801
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1802 | h1802
                        · rcases h5bigk with h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c | h1803c
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [hlam, p1803_0]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1103, hlam, p1803_1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1338, hlam, p1803_0]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1632, hlam, p1803_0]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1338, h1764, h1765, h1799, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1803_1, u4elo1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1765, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1803_1, u4elo1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [hlam, p1803_0]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1765, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1803_1, u4elo1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1765, h1799, hc23, hlam, hphi, ht34, p1803_1, u4elo1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1765, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1803_1, u4elo1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1103, hc01, hc25, hlam, hphi, ht12, p1803_1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1762, hlam, p1803_1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [hlam, p1803_0]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1799, hlam, p1803_1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1762, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1803_1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1103, hc01, hc35, hlam, hphi, ht12, ht23, p1803_1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1764, hlam, p1803_1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1764, h1765, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1803_1, u4elo1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [hlam, p1803_0]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1764, h1765, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1803_1, u4elo1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1760, hlam, p1803_1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1765, hlam, p1803_1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1801, hlam, p1803_1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [h1802, hlam, p1803_1]
                          · have p1803_0 := h1803c.1
                            have p1803_1 := h1803c.2.1
                            have p1803_2 := h1803c.2.2.1
                            have p1803_3 := h1803c.2.2.2
                            linarith only [hlam, p1803_0]
                        · linarith only [h0, h1760, h1766, h1802, hc24, hlam, hphi, u4elo1]
                      · linarith only [h0, h1760, h1766, h1801, hc23, hlam, hphi, ht34, u4elo1]
                · linarith only [h0, h1760, h1765, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1832 | h1832
                · linarith only [h1763, h1764, h1832, hlam]
                · linarith only [h0, h1760, h1832, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1835 | h1835
              · linarith only [h1632, h1763, h1835, hc03, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1837 | h1837
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1838 | h1838
                  · linarith only [h1761, h1763, h1838, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1840 | h1840
                    · linarith only [h1761, h1835, h1840, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1842 | h1842
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1843 | h1843
                        · rcases h5bigk with h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [hlam, p1844_0]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1103, hlam, p1844_1]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1338, hlam, p1844_0]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1632, hlam, p1844_0]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1103, h1837, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1844_1, u4elo1]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1837, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1844_1, u4elo1]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [hlam, p1844_0]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1338, h1837, hc02, hlam, hphi, ht23, ht34, p1844_1, u4elo1]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1835, hlam, p1844_0]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1763, h1837, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1844_1, u4elo3]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1103, hc01, hc25, hlam, hphi, ht12, p1844_1]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1762, hlam, p1844_1]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [hlam, p1844_0]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1840, hlam, p1844_1]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1762, h1763, h1837, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1844_1, u4elo3]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1103, h1843, hc01, hlam, hphi, ht12, ht23, ht34, p1844_1, u4elo3]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1843, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1844_1, u4elo3]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1338, h1843, hc02, hlam, hphi, ht23, ht34, p1844_1, u4elo3]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [hlam, p1844_0]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1843, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1844_1, u4elo3]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1760, hlam, p1844_1]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1837, hlam, p1844_1]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1842, hlam, p1844_1]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [h1843, hlam, p1844_1]
                          · have p1844_0 := h1844c.1
                            have p1844_1 := h1844c.2.1
                            have p1844_2 := h1844c.2.2.1
                            have p1844_3 := h1844c.2.2.2
                            linarith only [hlam, p1844_0]
                        · linarith only [h0, h1763, h1843, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h1760, h1842, hc24, hlam, hphi, u4elo0]
                · linarith only [h0, h1837, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1873 | h1873
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1874 | h1874
              · linarith only [h1761, h1762, h1874, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1876 | h1876
                · linarith only [h1761, h1762, h1873, h1876, hlam]
                · linarith only [h0, h1760, h1876, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1879 | h1879
              · linarith only [h1632, h1873, h1879, hc03, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1881 | h1881
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1882 | h1882
                  · linarith only [h1761, h1762, h1873, h1881, h1882, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1884 | h1884
                    · linarith only [h1761, h1762, h1873, h1879, h1881, h1884, hc13, hlam, hphi, ht34, u4elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1886 | h1886
                      · linarith only [h1761, h1762, h1886, hc23, hlam, hphi, ht34, u4elo2]
                      · linarith only [h0, h1760, h1873, h1886, hc24, hlam, hphi, u4elo3]
                · linarith only [h0, h1760, h1881, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1890 | h1890
          · linarith only [h1338, h1761, h1890, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1892 | h1892
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1893 | h1893
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1894 | h1894
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1895 | h1895
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1896 | h1896
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1897 | h1897
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1898 | h1898
                        · rcases h5bigk with h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c | h1899c
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [hlam, p1899_0]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1103, hlam, p1899_1]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1338, hlam, p1899_0]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1632, hlam, p1899_0]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1103, h1890, h1897, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1899_1, u4elo2]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1890, h1897, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1899_1, u4elo2]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [hlam, p1899_0]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1890, hlam, p1899_0]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1632, h1890, h1897, hc03, hlam, hphi, ht34, p1899_1, u4elo2]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1890, h1897, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1899_1, u4elo2]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1103, h1897, hc01, hlam, hphi, ht12, ht23, ht34, p1899_1, u4elo2]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1897, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1899_1, u4elo2]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [hlam, p1899_0]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1632, h1897, hc03, hlam, hphi, ht34, p1899_1, u4elo2]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1897, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1899_1, u4elo2]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1103, h1893, hc01, hc13, hlam, hphi, p1899_1]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1893, hlam, p1899_1]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1896, hlam, p1899_0]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [hlam, p1899_0]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1898, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1899_1, u4elo3]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1760, hlam, p1899_1]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1894, hlam, p1899_1]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1897, hlam, p1899_1]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [h1898, hlam, p1899_1]
                          · have p1899_0 := h1899c.1
                            have p1899_1 := h1899c.2.1
                            have p1899_2 := h1899c.2.2.1
                            have p1899_3 := h1899c.2.2.2
                            linarith only [hlam, p1899_0]
                        · linarith only [h0, h1760, h1898, hc34, hlam, hphi, u4elo1]
                      · linarith only [h0, h1760, h1897, hc24, hlam, hphi, u4elo1]
                    · linarith only [h1761, h1893, h1894, h1896, hc12, hlam, hphi, ht23, ht34, u4elo1]
                  · linarith only [h1632, h1761, h1893, h1895, hc03, hc34, hlam, hphi]
                · linarith only [h0, h1894, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1930 | h1930
                · linarith only [h1892, h1893, h1930, hlam]
                · linarith only [h0, h1760, h1930, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1933 | h1933
              · linarith only [h1632, h1892, h1933, hc03, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1935 | h1935
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1936 | h1936
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1937 | h1937
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1938 | h1938
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1939 | h1939
                        · rcases h5bigk with h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c | h1940c
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [hlam, p1940_0]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1103, hlam, p1940_1]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1338, hlam, p1940_0]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1632, hlam, p1940_0]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1103, h1892, h1935, h1936, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1940_1, u4elo2]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1892, h1935, h1936, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1940_1, u4elo2]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [hlam, p1940_0]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1890, hlam, p1940_0]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1933, hlam, p1940_0]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1892, h1935, h1936, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1940_1, u4elo2]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1103, h1938, hc01, hlam, hphi, ht12, ht23, ht34, p1940_1, u4elo2]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1938, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1940_1, u4elo2]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [hlam, p1940_0]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1933, h1938, hc13, hlam, hphi, ht34, p1940_1, u4elo2]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1938, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1940_1, u4elo2]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1103, hc01, hc35, hlam, hphi, ht12, ht23, p1940_1]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1103, hc01, hc35, hlam, hphi, ht12, ht23, p1940_1]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1937, hlam, p1940_0]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [hlam, p1940_0]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1937, h1938, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1940_1, u4elo2]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1760, hlam, p1940_1]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1935, hlam, p1940_1]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1938, hlam, p1940_1]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [h1939, hlam, p1940_1]
                          · have p1940_0 := h1940c.1
                            have p1940_1 := h1940c.2.1
                            have p1940_2 := h1940c.2.2.1
                            have p1940_3 := h1940c.2.2.2
                            linarith only [hlam, p1940_0]
                        · linarith only [h0, h1892, h1939, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                      · linarith only [h1760, h1938, hc24, hlam, hphi, u4elo0]
                    · linarith only [h1103, h1892, h1935, h1936, h1937, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h1761, h1936, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h0, h1760, h1935, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1971 | h1971
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1972 | h1972
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1973 | h1973
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1974 | h1974
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1975 | h1975
                · linarith only [h0, h1760, h1975, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h1975, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1978 | h1978
                · linarith only [h0, h1760, h1978, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h1978, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1981 | h1981
              · linarith only [h1632, h1973, h1981, hc03, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1983 | h1983
                · linarith only [h0, h1760, h1983, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h1983, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1986 | h1986
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1987 | h1987
              · linarith only [h1971, h1972, h1987, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1989 | h1989
                · linarith only [h0, h1760, h1989, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h1989, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1992 | h1992
              · linarith only [h1632, h1986, h1992, hc03, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1994 | h1994
                · linarith only [h0, h1760, h1994, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h1994, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1997 | h1997
          · linarith only [h1338, h1971, h1997, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1999 | h1999
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2000 | h2000
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2001 | h2001
                · linarith only [h0, h1760, h2001, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h2001, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2004 | h2004
                · linarith only [h0, h1760, h2004, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h2004, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2007 | h2007
              · linarith only [h1632, h1999, h2007, hc03, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2009 | h2009
                · linarith only [h0, h1760, h2009, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h0, h2009, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]

set_option maxHeartbeats 4024000 in
set_option maxHeartbeats 4024000 in
theorem r1l7_14_25_L_0_H_I_x1 (m : N7Model)
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1103 | h1103
  · exact r1l7_14_25_L_0_H_I_x1_x0 m hb4 hb5 h0 h1103
  · exact r1l7_14_25_L_0_H_I_x1_x1 m hb4 hb5 h0 h1103

set_option maxHeartbeats 4024000 in
set_option maxHeartbeats 4024000 in
theorem r1l7_14_25_L_0_H_I (m : N7Model)
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · exact r1l7_14_25_L_0_H_I_x0 m hb4 hb5 h0
  · exact r1l7_14_25_L_0_H_I_x1 m hb4 hb5 h0

end R2N4
