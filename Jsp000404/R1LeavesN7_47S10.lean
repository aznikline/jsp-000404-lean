import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5884000 in
set_option maxHeartbeats 5884000 in
theorem r1l7_22_14_M_IR_L_I_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h664 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1335 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1336 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1337 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1338 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1340 | h1340
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1341 | h1341
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1342 | h1342
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1343 | h1343
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1344 | h1344
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1345 | h1345
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1346 | h1346
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1347 | h1347
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1348 | h1348
                  · rcases h2bigk with h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h0, hlam, p1349_1]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h0, h1345, h1348, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1349_1]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      rcases p1349_3 (m.d 0 2) (by simp) with h1353 | h1353
                      · rcases p1349_3 (m.d 1 2) (by simp) with h1354 | h1354
                        · rcases p1349_3 (m.d 2 3) (by simp) with h1355 | h1355
                          · linarith only [h1335, h1355, hlam]
                          · linarith only [h1345, h1355, hlam]
                        · linarith only [h1341, h1354, hlam]
                      · linarith only [h1353, hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      rcases p1349_3 (m.d 0 2) (by simp) with h1360 | h1360
                      · rcases p1349_3 (m.d 1 2) (by simp) with h1361 | h1361
                        · rcases p1349_3 (m.d 2 3) (by simp) with h1362 | h1362
                          · linarith only [h1335, h1362, hlam]
                          · linarith only [h1346, h1362, hlam]
                        · linarith only [h1342, h1361, hlam]
                      · linarith only [h1360, hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1335, h1345, h1348, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1349_1]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1345, h1348, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1349_1]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      rcases p1349_3 (m.d 0 2) (by simp) with h1370 | h1370
                      · linarith only [h0, h1370, hlam]
                      · linarith only [h1336, h1370, hlam]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      rcases p1349_3 (m.d 0 2) (by simp) with h1373 | h1373
                      · linarith only [h0, h1373, hlam]
                      · linarith only [h1337, h1373, hlam]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1335, hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1340, hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1335, h1347, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1349_1, u2ehi4]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h0, h1335, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1349_1, u2ehi4]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1336, hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1341, hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1345, hlam, p1349_1]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [hc24, hlam, hphi, p1349_1, u2ehi4]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1337, hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1342, hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1346, hlam, p1349_1]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [h1347, hlam, p1349_0]
                    · have p1349_0 := h1349c.1
                      have p1349_1 := h1349c.2.1
                      have p1349_2 := h1349c.2.2.1
                      have p1349_3 := h1349c.2.2.2
                      linarith only [hlam, p1349_0]
                  · rcases h2bigk with h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h0, hlam, p1391_1]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h0, h1345, h1347, h1348, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1391_1]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h0, h1347, h1348, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1391_1]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      rcases p1391_3 (m.d 0 2) (by simp) with h1396 | h1396
                      · rcases p1391_3 (m.d 1 2) (by simp) with h1397 | h1397
                        · rcases p1391_3 (m.d 2 3) (by simp) with h1398 | h1398
                          · linarith only [h1335, h1398, hlam]
                          · linarith only [h1346, h1398, hlam]
                        · linarith only [h1342, h1397, hlam]
                      · linarith only [h1396, hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1335, h1345, h1347, h1348, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1391_1]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1345, h1347, h1348, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1391_1]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1347, h1348, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1391_1]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      rcases p1391_3 (m.d 0 2) (by simp) with h1407 | h1407
                      · linarith only [h0, h1407, hlam]
                      · linarith only [h1337, h1407, hlam]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1335, hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1340, hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1335, h1347, h1348, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1391_1]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h0, h1335, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1391_1, u2ehi4]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1336, hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1341, hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1345, hlam, p1391_1]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [hc24, hlam, hphi, p1391_1, u2ehi4]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1337, hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1342, hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1346, hlam, p1391_1]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [h1347, hlam, p1391_0]
                    · have p1391_0 := h1391c.1
                      have p1391_1 := h1391c.2.1
                      have p1391_2 := h1391c.2.2.1
                      have p1391_3 := h1391c.2.2.2
                      linarith only [hlam, p1391_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1425 | h1425
                  · linarith only [h1345, h1347, h1425, hlam]
                  · rcases h2bigk with h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h0, hlam, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      rcases p1427_3 (m.d 0 2) (by simp) with h1430 | h1430
                      · rcases p1427_3 (m.d 1 2) (by simp) with h1431 | h1431
                        · rcases p1427_3 (m.d 2 3) (by simp) with h1432 | h1432
                          · linarith only [h1432, hlam, p1427_0]
                          · rcases p1427_3 (m.d 2 4) (by simp) with h1434 | h1434
                            · linarith only [h1336, h1434, hlam]
                            · rcases p1427_3 (m.d 2 5) (by simp) with h1436 | h1436
                              · linarith only [h1337, h1436, hlam]
                              · rcases h4bigk with h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c | h1438c
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [hlam, p1438_0]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h664, hlam, p1438_0]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  rcases p1438_3 (m.d 0 4) (by simp) with h1441 | h1441
                                  · rcases p1438_3 (m.d 1 4) (by simp) with h1442 | h1442
                                    · rcases p1438_3 (m.d 2 4) (by simp) with h1443 | h1443
                                      · linarith only [h1336, h1443, hlam]
                                      · rcases p1438_3 (m.d 3 4) (by simp) with h1445 | h1445
                                        · linarith only [h1338, h1445, hlam]
                                        · rcases p1438_3 (m.d 4 5) (by simp) with h1447 | h1447
                                          · linarith only [h1339, h1447, hlam]
                                          · linarith only [h1347, h1447, hlam]
                                    · linarith only [h1341, h1442, hlam]
                                  · linarith only [h1336, h1441, hlam]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  rcases p1438_3 (m.d 0 4) (by simp) with h1452 | h1452
                                  · rcases p1438_3 (m.d 1 4) (by simp) with h1453 | h1453
                                    · rcases p1438_3 (m.d 2 4) (by simp) with h1454 | h1454
                                      · linarith only [h1336, h1454, hlam]
                                      · linarith only [h1345, h1454, hlam]
                                    · linarith only [h1343, h1453, hlam]
                                  · linarith only [h1338, h1452, hlam]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1340, h1343, h1347, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1438_1, u2ehi3]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1339, h1340, h1343, h1347, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1438_1, u2ehi3]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [hlam, p1438_0]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  rcases p1438_3 (m.d 0 4) (by simp) with h1462 | h1462
                                  · linarith only [h1462, h664, hlam]
                                  · linarith only [h1336, h1462, hlam]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  rcases p1438_3 (m.d 0 4) (by simp) with h1465 | h1465
                                  · linarith only [h1465, h664, hlam]
                                  · linarith only [h1338, h1465, hlam]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1347, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1438_1, u2ehi3]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1336, hlam, p1438_1]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1341, hlam, p1438_1]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [hlam, p1438_0]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1339, h1347, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1438_1]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1347, hlam, p1438_0]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1338, hlam, p1438_1]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1343, hlam, p1438_0]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1345, hlam, p1438_0]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [hlam, p1438_0]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1425, hlam, p1438_0]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1339, hlam, p1438_0]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1344, hlam, p1438_0]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [h1339, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1438_1, u2ehi3]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  rcases p1438_3 (m.d 0 4) (by simp) with h1482 | h1482
                                  · rcases p1438_3 (m.d 1 4) (by simp) with h1483 | h1483
                                    · rcases p1438_3 (m.d 2 4) (by simp) with h1484 | h1484
                                      · linarith only [h1347, h1484, hlam]
                                      · linarith only [h1345, h1484, hlam]
                                    · linarith only [h1343, h1483, hlam]
                                  · linarith only [h1338, h1482, hlam]
                                · have p1438_0 := h1438c.1
                                  have p1438_1 := h1438c.2.1
                                  have p1438_2 := h1438c.2.2.1
                                  have p1438_3 := h1438c.2.2.2
                                  linarith only [hlam, p1438_0]
                        · linarith only [h1340, h1431, hlam]
                      · linarith only [h1430, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      rcases p1427_3 (m.d 0 2) (by simp) with h1492 | h1492
                      · rcases p1427_3 (m.d 1 2) (by simp) with h1493 | h1493
                        · rcases p1427_3 (m.d 2 3) (by simp) with h1494 | h1494
                          · linarith only [h1335, h1494, hlam]
                          · linarith only [h1345, h1494, hlam]
                        · linarith only [h1341, h1493, hlam]
                      · linarith only [h1492, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      rcases p1427_3 (m.d 0 2) (by simp) with h1499 | h1499
                      · rcases p1427_3 (m.d 1 2) (by simp) with h1500 | h1500
                        · rcases p1427_3 (m.d 2 3) (by simp) with h1501 | h1501
                          · linarith only [h1335, h1501, hlam]
                          · linarith only [h1346, h1501, hlam]
                        · linarith only [h1342, h1500, hlam]
                      · linarith only [h1499, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1335, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1427_1, u2ehi2]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      rcases p1427_3 (m.d 0 2) (by simp) with h1508 | h1508
                      · linarith only [h0, h1508, hlam]
                      · linarith only [h1335, h1508, hlam]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      rcases p1427_3 (m.d 0 2) (by simp) with h1511 | h1511
                      · linarith only [h0, h1511, hlam]
                      · linarith only [h1336, h1511, hlam]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      rcases p1427_3 (m.d 0 2) (by simp) with h1514 | h1514
                      · linarith only [h0, h1514, hlam]
                      · linarith only [h1337, h1514, hlam]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1335, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1340, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hc23, hlam, hphi, p1427_1, u2ehi3]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h0, h1335, h1347, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1427_1, u2ehi3]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1336, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1341, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1345, hlam, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1347, hlam, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1337, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1342, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1346, hlam, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hc25, hlam, hphi, p1427_1, u2ehi3]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hlam, p1427_0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1532 | h1532
                · linarith only [h1345, h1346, h1532, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1534 | h1534
                  · linarith only [h1532, h1534, hc34, hlam, hphi, ht23, u2ehi3]
                  · rcases h2bigk with h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c | h1536c
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h0, hlam, p1536_1]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      rcases p1536_3 (m.d 0 2) (by simp) with h1539 | h1539
                      · rcases p1536_3 (m.d 1 2) (by simp) with h1540 | h1540
                        · rcases p1536_3 (m.d 2 3) (by simp) with h1541 | h1541
                          · linarith only [h1541, hlam, p1536_0]
                          · rcases p1536_3 (m.d 2 4) (by simp) with h1543 | h1543
                            · linarith only [h1336, h1543, hlam]
                            · rcases p1536_3 (m.d 2 5) (by simp) with h1545 | h1545
                              · linarith only [h1337, h1545, hlam]
                              · linarith only [h1346, h1545, hlam]
                        · linarith only [h1340, h1540, hlam]
                      · linarith only [h1539, hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      rcases p1536_3 (m.d 0 2) (by simp) with h1550 | h1550
                      · rcases p1536_3 (m.d 1 2) (by simp) with h1551 | h1551
                        · rcases p1536_3 (m.d 2 3) (by simp) with h1552 | h1552
                          · linarith only [h1335, h1552, hlam]
                          · linarith only [h1345, h1552, hlam]
                        · linarith only [h1341, h1551, hlam]
                      · linarith only [h1550, hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      rcases p1536_3 (m.d 0 2) (by simp) with h1557 | h1557
                      · rcases p1536_3 (m.d 1 2) (by simp) with h1558 | h1558
                        · rcases p1536_3 (m.d 2 3) (by simp) with h1559 | h1559
                          · linarith only [h1335, h1559, hlam]
                          · rcases p1536_3 (m.d 2 4) (by simp) with h1561 | h1561
                            · linarith only [h1336, h1561, hlam]
                            · rcases p1536_3 (m.d 2 5) (by simp) with h1563 | h1563
                              · linarith only [h1563, hlam, p1536_0]
                              · rcases h4bigk with h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c | h1565c
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h664, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  rcases p1565_3 (m.d 0 4) (by simp) with h1568 | h1568
                                  · rcases p1565_3 (m.d 1 4) (by simp) with h1569 | h1569
                                    · rcases p1565_3 (m.d 2 4) (by simp) with h1570 | h1570
                                      · linarith only [h1336, h1570, hlam]
                                      · rcases p1565_3 (m.d 3 4) (by simp) with h1572 | h1572
                                        · linarith only [h1338, h1572, hlam]
                                        · rcases p1565_3 (m.d 4 5) (by simp) with h1574 | h1574
                                          · linarith only [h1339, h1574, hlam]
                                          · linarith only [h1532, h1574, hlam]
                                    · linarith only [h1341, h1569, hlam]
                                  · linarith only [h1336, h1568, hlam]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1339, h1345, h1346, h1534, hlam, p1565_2]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1345, h1346, h1534, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1565_1, u2ehi3]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1339, h1340, h1343, h1345, h1346, h1534, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1565_1, u2ehi3]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  rcases p1565_3 (m.d 0 4) (by simp) with h1583 | h1583
                                  · linarith only [h1583, h664, hlam]
                                  · linarith only [h1336, h1583, hlam]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1339, h1345, h1346, h1534, h664, hlam, p1565_2]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1345, h1346, h1534, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1565_1, u2ehi3]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1336, hlam, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1341, hlam, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1339, h1345, h1346, h1534, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1532, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1338, hlam, p1565_1]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1343, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1345, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1534, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1339, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1344, hlam, p1565_0]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [h1339, h1340, h1343, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1565_1, u2ehi3]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  rcases p1565_3 (m.d 0 4) (by simp) with h1601 | h1601
                                  · rcases p1565_3 (m.d 1 4) (by simp) with h1602 | h1602
                                    · rcases p1565_3 (m.d 2 4) (by simp) with h1603 | h1603
                                      · linarith only [h1532, h1603, hlam]
                                      · linarith only [h1345, h1603, hlam]
                                    · linarith only [h1343, h1602, hlam]
                                  · linarith only [h1338, h1601, hlam]
                                · have p1565_0 := h1565c.1
                                  have p1565_1 := h1565c.2.1
                                  have p1565_2 := h1565c.2.2.1
                                  have p1565_3 := h1565c.2.2.2
                                  linarith only [hlam, p1565_0]
                        · linarith only [h1342, h1558, hlam]
                      · linarith only [h1557, hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h1335, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1536_1, u2ehi2]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      rcases p1536_3 (m.d 0 2) (by simp) with h1613 | h1613
                      · linarith only [h0, h1613, hlam]
                      · linarith only [h1335, h1613, hlam]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      rcases p1536_3 (m.d 0 2) (by simp) with h1616 | h1616
                      · linarith only [h0, h1616, hlam]
                      · linarith only [h1336, h1616, hlam]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      rcases p1536_3 (m.d 0 2) (by simp) with h1619 | h1619
                      · linarith only [h0, h1619, hlam]
                      · linarith only [h1337, h1619, hlam]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h1335, hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h1340, hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [hc23, hlam, hphi, p1536_1, u2ehi3]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h1346, hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h1336, hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h1341, hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h1345, hlam, p1536_1]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h1532, hlam, p1536_1]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h1337, hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h1342, hlam, p1536_0]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [hc25, hlam, hphi, p1536_1, u2ehi2]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [h1339, h1340, h1343, h1346, h1534, h664, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1536_1, u2ehi3]
                    · have p1536_0 := h1536c.1
                      have p1536_1 := h1536c.2.1
                      have p1536_2 := h1536c.2.2.1
                      have p1536_3 := h1536c.2.2.2
                      linarith only [hlam, p1536_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1637 | h1637
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1638 | h1638
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1639 | h1639
                  · rcases h2bigk with h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c | h1640c
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h0, hlam, p1640_1]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      rcases p1640_3 (m.d 0 2) (by simp) with h1643 | h1643
                      · rcases p1640_3 (m.d 1 2) (by simp) with h1644 | h1644
                        · rcases p1640_3 (m.d 2 3) (by simp) with h1645 | h1645
                          · linarith only [h1645, hlam, p1640_0]
                          · rcases p1640_3 (m.d 2 4) (by simp) with h1647 | h1647
                            · linarith only [h1336, h1647, hlam]
                            · linarith only [h1345, h1647, hlam]
                        · linarith only [h1340, h1644, hlam]
                      · linarith only [h1643, hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      rcases p1640_3 (m.d 0 2) (by simp) with h1652 | h1652
                      · rcases p1640_3 (m.d 1 2) (by simp) with h1653 | h1653
                        · rcases p1640_3 (m.d 2 3) (by simp) with h1654 | h1654
                          · linarith only [h1335, h1654, hlam]
                          · rcases p1640_3 (m.d 2 4) (by simp) with h1656 | h1656
                            · linarith only [h1656, hlam, p1640_0]
                            · rcases p1640_3 (m.d 2 5) (by simp) with h1658 | h1658
                              · linarith only [h1337, h1658, hlam]
                              · rcases h4bigk with h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c | h1660c
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h664, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  rcases p1660_3 (m.d 0 4) (by simp) with h1663 | h1663
                                  · rcases p1660_3 (m.d 1 4) (by simp) with h1664 | h1664
                                    · rcases p1660_3 (m.d 2 4) (by simp) with h1665 | h1665
                                      · linarith only [h1336, h1665, hlam]
                                      · rcases p1660_3 (m.d 3 4) (by simp) with h1667 | h1667
                                        · linarith only [h1338, h1667, hlam]
                                        · linarith only [h1345, h1667, hlam]
                                    · linarith only [h1341, h1664, hlam]
                                  · linarith only [h1336, h1663, hlam]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1340, h1343, h1345, h1637, h664, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1660_1]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  rcases p1660_3 (m.d 0 4) (by simp) with h1673 | h1673
                                  · rcases p1660_3 (m.d 1 4) (by simp) with h1674 | h1674
                                    · rcases p1660_3 (m.d 2 4) (by simp) with h1675 | h1675
                                      · linarith only [h1336, h1675, hlam]
                                      · linarith only [h1638, h1675, hlam]
                                    · linarith only [h1344, h1674, hlam]
                                  · linarith only [h1673, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1338, h1340, h1343, h1345, h1637, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1660_1]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  rcases p1660_3 (m.d 0 4) (by simp) with h1682 | h1682
                                  · linarith only [h1682, h664, hlam]
                                  · linarith only [h1336, h1682, hlam]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1340, h1343, h1345, h1637, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1660_1, u2ehi4]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  rcases p1660_3 (m.d 0 4) (by simp) with h1686 | h1686
                                  · linarith only [h1686, h664, hlam]
                                  · linarith only [h1339, h1686, hlam]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1336, hlam, p1660_1]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1341, hlam, p1660_1]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1345, hlam, p1660_1]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1640_1, p1660_1]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1338, hlam, p1660_1]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1343, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hc34, hlam, hphi, ht23, p1660_1, u2ehi3]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  rcases p1660_3 (m.d 0 4) (by simp) with h1698 | h1698
                                  · rcases p1660_3 (m.d 1 4) (by simp) with h1699 | h1699
                                    · rcases p1660_3 (m.d 2 4) (by simp) with h1700 | h1700
                                      · linarith only [h1345, h1700, hlam]
                                      · linarith only [h1638, h1700, hlam]
                                    · linarith only [h1344, h1699, hlam]
                                  · linarith only [h1339, h1698, hlam]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1339, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1344, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1638, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [h1639, hlam, p1660_0]
                                · have p1660_0 := h1660c.1
                                  have p1660_1 := h1660c.2.1
                                  have p1660_2 := h1660c.2.2.1
                                  have p1660_3 := h1660c.2.2.2
                                  linarith only [hlam, p1660_0]
                        · linarith only [h1341, h1653, hlam]
                      · linarith only [h1652, hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      rcases p1640_3 (m.d 0 2) (by simp) with h1712 | h1712
                      · rcases p1640_3 (m.d 1 2) (by simp) with h1713 | h1713
                        · rcases p1640_3 (m.d 2 3) (by simp) with h1714 | h1714
                          · linarith only [h1335, h1714, hlam]
                          · linarith only [h1637, h1714, hlam]
                        · linarith only [h1342, h1713, hlam]
                      · linarith only [h1712, hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h1335, h1637, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1640_1, u2ehi4]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      rcases p1640_3 (m.d 0 2) (by simp) with h1721 | h1721
                      · linarith only [h0, h1721, hlam]
                      · linarith only [h1335, h1721, hlam]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      rcases p1640_3 (m.d 0 2) (by simp) with h1724 | h1724
                      · linarith only [h0, h1724, hlam]
                      · linarith only [h1336, h1724, hlam]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      rcases p1640_3 (m.d 0 2) (by simp) with h1727 | h1727
                      · linarith only [h0, h1727, hlam]
                      · linarith only [h1337, h1727, hlam]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h1335, hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h1340, hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h1345, hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h1335, h1338, h1345, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1640_1, u2ehi4]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h1336, hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h1341, hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [hc24, hlam, hphi, p1640_1, u2ehi2]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h0, h1335, h1338, h1345, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1640_1, u2ehi4]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h1337, hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h1342, hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h1637, hlam, p1640_1]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [h1638, hlam, p1640_0]
                    · have p1640_0 := h1640c.1
                      have p1640_1 := h1640c.2.1
                      have p1640_2 := h1640c.2.2.1
                      have p1640_3 := h1640c.2.2.2
                      linarith only [hlam, p1640_0]
                  · linarith only [h1345, h1639, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · linarith only [h1345, h1637, h1638, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1747 | h1747
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1748 | h1748
                  · rcases h2bigk with h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h0, hlam, p1749_1]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      rcases p1749_3 (m.d 0 2) (by simp) with h1752 | h1752
                      · rcases p1749_3 (m.d 1 2) (by simp) with h1753 | h1753
                        · rcases p1749_3 (m.d 2 3) (by simp) with h1754 | h1754
                          · linarith only [h1754, hlam, p1749_0]
                          · rcases p1749_3 (m.d 2 4) (by simp) with h1756 | h1756
                            · linarith only [h1336, h1756, hlam]
                            · linarith only [h1345, h1756, hlam]
                        · linarith only [h1340, h1753, hlam]
                      · linarith only [h1752, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      rcases p1749_3 (m.d 0 2) (by simp) with h1761 | h1761
                      · rcases p1749_3 (m.d 1 2) (by simp) with h1762 | h1762
                        · rcases p1749_3 (m.d 2 3) (by simp) with h1763 | h1763
                          · linarith only [h1335, h1763, hlam]
                          · rcases p1749_3 (m.d 2 4) (by simp) with h1765 | h1765
                            · linarith only [h1765, hlam, p1749_0]
                            · rcases p1749_3 (m.d 2 5) (by simp) with h1767 | h1767
                              · linarith only [h1337, h1767, hlam]
                              · rcases h4bigk with h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c | h1769c
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [hlam, p1769_0]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h664, hlam, p1769_0]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  rcases p1769_3 (m.d 0 4) (by simp) with h1772 | h1772
                                  · rcases p1769_3 (m.d 1 4) (by simp) with h1773 | h1773
                                    · rcases p1769_3 (m.d 2 4) (by simp) with h1774 | h1774
                                      · linarith only [h1336, h1774, hlam]
                                      · rcases p1769_3 (m.d 3 4) (by simp) with h1776 | h1776
                                        · linarith only [h1338, h1776, hlam]
                                        · linarith only [h1345, h1776, hlam]
                                    · linarith only [h1341, h1773, hlam]
                                  · linarith only [h1336, h1772, hlam]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1345, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1769_1, u2ehi2]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  rcases p1769_3 (m.d 0 4) (by simp) with h1782 | h1782
                                  · rcases p1769_3 (m.d 1 4) (by simp) with h1783 | h1783
                                    · rcases p1769_3 (m.d 2 4) (by simp) with h1784 | h1784
                                      · linarith only [h1336, h1784, hlam]
                                      · linarith only [h1747, h1784, hlam]
                                    · linarith only [h1344, h1783, hlam]
                                  · linarith only [h1782, hlam, p1769_0]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1338, h1340, h1343, h1637, h1748, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1769_1, u2ehi2]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [hlam, p1769_0]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  rcases p1769_3 (m.d 0 4) (by simp) with h1791 | h1791
                                  · linarith only [h1791, h664, hlam]
                                  · linarith only [h1336, h1791, hlam]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1340, h1343, h1637, h1748, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1769_1, u2ehi2]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  rcases p1769_3 (m.d 0 4) (by simp) with h1795 | h1795
                                  · linarith only [h1795, h664, hlam]
                                  · linarith only [h1339, h1795, hlam]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1336, hlam, p1769_1]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1341, hlam, p1769_1]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [hlam, p1769_0]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1345, hlam, p1769_1]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1749_1, p1769_1]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1338, hlam, p1769_1]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1343, hlam, p1769_0]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [hc34, hlam, hphi, ht23, p1769_1, u2ehi3]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [hlam, p1769_0]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  rcases p1769_3 (m.d 0 4) (by simp) with h1807 | h1807
                                  · rcases p1769_3 (m.d 1 4) (by simp) with h1808 | h1808
                                    · rcases p1769_3 (m.d 2 4) (by simp) with h1809 | h1809
                                      · linarith only [h1345, h1809, hlam]
                                      · linarith only [h1747, h1809, hlam]
                                    · linarith only [h1344, h1808, hlam]
                                  · linarith only [h1339, h1807, hlam]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1339, hlam, p1769_0]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1344, hlam, p1769_0]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1747, hlam, p1769_0]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [h1748, hlam, p1769_0]
                                · have p1769_0 := h1769c.1
                                  have p1769_1 := h1769c.2.1
                                  have p1769_2 := h1769c.2.2.1
                                  have p1769_3 := h1769c.2.2.2
                                  linarith only [hlam, p1769_0]
                        · linarith only [h1341, h1762, hlam]
                      · linarith only [h1761, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      rcases p1749_3 (m.d 0 2) (by simp) with h1821 | h1821
                      · rcases p1749_3 (m.d 1 2) (by simp) with h1822 | h1822
                        · rcases p1749_3 (m.d 2 3) (by simp) with h1823 | h1823
                          · linarith only [h1335, h1823, hlam]
                          · rcases p1749_3 (m.d 2 4) (by simp) with h1825 | h1825
                            · linarith only [h1336, h1825, hlam]
                            · linarith only [h1747, h1825, hlam]
                        · linarith only [h1342, h1822, hlam]
                      · linarith only [h1821, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h1335, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1749_1, u2ehi2]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      rcases p1749_3 (m.d 0 2) (by simp) with h1832 | h1832
                      · linarith only [h0, h1832, hlam]
                      · linarith only [h1335, h1832, hlam]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      rcases p1749_3 (m.d 0 2) (by simp) with h1835 | h1835
                      · linarith only [h0, h1835, hlam]
                      · linarith only [h1336, h1835, hlam]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      rcases p1749_3 (m.d 0 2) (by simp) with h1838 | h1838
                      · linarith only [h0, h1838, hlam]
                      · linarith only [h1337, h1838, hlam]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h1335, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h1340, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h1345, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h1637, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h1336, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h1341, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [hc24, hlam, hphi, p1749_1, u2ehi2]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h1338, h1345, h1637, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1749_1, u2ehi2]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h1337, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h1342, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [hc25, hlam, hphi, p1749_1, u2ehi2]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [h1747, hlam, p1749_0]
                    · have p1749_0 := h1749c.1
                      have p1749_1 := h1749c.2.1
                      have p1749_2 := h1749c.2.2.1
                      have p1749_3 := h1749c.2.2.2
                      linarith only [hlam, p1749_0]
                  · linarith only [h0, h1335, h1338, h1339, h1345, h1748, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1857 | h1857
                  · linarith only [h0, h1335, h1338, h1747, h1857, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · linarith only [h1345, h1857, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h1339, h1344, h664, hlam]
        · linarith only [h1338, h1343, h664, hlam]
      · linarith only [h0, h1335, h1342, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1335, h1341, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, h1335, h1340, hlam]

end R2N4
