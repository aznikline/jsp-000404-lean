import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_30S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1307 | h1307
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1308 | h1308
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1309 | h1309
      · linarith only [h0, h1309, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1311 | h1311
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1312 | h1312
          · linarith only [h0, h1307, h1312, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1314 | h1314
            · linarith only [h0, h1307, h1311, h1314, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1316 | h1316
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1317 | h1317
                · linarith only [h0, h1314, h1316, h1317, h3, hc34, hc45, hlam, hphi]
                · linarith only [h1311, h1312, h1317, hc23, hc35, hlam, hphi]
              · linarith only [h1307, h1309, h1316, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1321 | h1321
          · linarith only [h1, h1321, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1323 | h1323
            · linarith only [h0, h1308, h1323, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1325 | h1325
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1326 | h1326
                · linarith only [h0, h1311, h1325, h1326, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases h0bigk with h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [hlam, p1328_0]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1, h1325, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h3, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h3, hlam, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h0, hlam, p1328_0]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [hlam, p1328_0]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h0, h1, h1325, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h0, h2, h3, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1309, hlam, p1328_0]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1, hlam, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1307, hlam, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [hlam, p1328_0]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1311, hlam, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1321, hlam, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h2, hlam, p1328_0]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1308, hlam, p1328_0]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1, h1325, h2, h3, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [hlam, p1328_0]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1323, hlam, p1328_0]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1323, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1323, hc02, hc45, hlam, hphi, ht23, ht34, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1, h1323, h1325, hc23, hc45, hlam, hphi, ht34, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [h1323, hc04, hc45, hlam, hphi, p1328_1]
                  · have p1328_0 := h1328c.1
                    have p1328_1 := h1328c.2.1
                    have p1328_2 := h1328c.2.2.1
                    have p1328_3 := h1328c.2.2.2
                    linarith only [hlam, p1328_0]
              · linarith only [h1307, h1309, h1325, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1355 | h1355
      · linarith only [h1308, h1355, h2, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1357 | h1357
        · linarith only [h1307, h1308, h1357, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1359 | h1359
          · linarith only [h1307, h1308, h1359, h2, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1361 | h1361
            · linarith only [h1361, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1363 | h1363
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1364 | h1364
                · linarith only [h0, h1363, h1364, h3, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases h0bigk with h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c | h1366c
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [hlam, p1366_0]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h3, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h3, hlam, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h0, hlam, p1366_0]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [hlam, p1366_0]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1, h1308, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1308, hlam, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1355, hlam, p1366_0]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1, hlam, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1307, hlam, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [hlam, p1366_0]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1357, hlam, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1359, hlam, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h2, hlam, p1366_0]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h0, h1363, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1, h2, h3, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [hlam, p1366_0]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1361, hlam, p1366_0]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1355, hc01, hc25, hlam, hphi, ht12, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h0, h1359, h1363, hc23, hc35, hlam, hphi, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1, h1359, hc13, hc35, hlam, hphi, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [h1361, hc04, hc45, hlam, hphi, p1366_1]
                  · have p1366_0 := h1366c.1
                    have p1366_1 := h1366c.2.1
                    have p1366_2 := h1366c.2.2.1
                    have p1366_3 := h1366c.2.2.2
                    linarith only [hlam, p1366_0]
              · linarith only [h1307, h1308, h1363, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1393 | h1393
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1394 | h1394
      · linarith only [h1, h1307, h1394, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1396 | h1396
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1397 | h1397
          · linarith only [h1, h1397, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1399 | h1399
            · linarith only [h1, h1307, h1393, h1399, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1401 | h1401
              · linarith only [h0, h1307, h1393, h1401, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1403 | h1403
                · rcases h0bigk with h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [hlam, p1404_0]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h3, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h3, hlam, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h0, hlam, p1404_0]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [hlam, p1404_0]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1307, hlam, p1404_0]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h0, h2, h3, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1394, hlam, p1404_0]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1, hlam, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [hlam, p1404_0]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1, h1393, h1403, h3, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1397, hlam, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h2, hlam, p1404_0]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1393, hlam, p1404_0]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1396, hlam, p1404_0]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [hlam, p1404_0]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1399, hlam, p1404_0]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1394, hc01, hc25, hlam, hphi, ht12, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1393, h1394, h1403, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1397, hc03, hc35, hlam, hphi, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [h1393, h1399, h1403, hc34, hc45, hlam, hphi, p1404_1]
                  · have p1404_0 := h1404c.1
                    have p1404_1 := h1404c.2.1
                    have p1404_2 := h1404c.2.2.1
                    have p1404_3 := h1404c.2.2.2
                    linarith only [hlam, p1404_0]
                · linarith only [h1, h1307, h1396, h1403, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h1307, h1393, h1396, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1432 | h1432
      · linarith only [h0, h1432, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1434 | h1434
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1435 | h1435
          · linarith only [h1, h1435, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1437 | h1437
            · linarith only [h1, h1434, h1437, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1439 | h1439
              · linarith only [h0, h1307, h1439, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1441 | h1441
                · rcases h0bigk with h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c | h1442c
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [hlam, p1442_0]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h3, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h3, hlam, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h0, hlam, p1442_0]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [hlam, p1442_0]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h1307, hlam, p1442_0]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h1393, hlam, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h1432, hlam, p1442_0]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h1, hlam, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h0, h1, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [hlam, p1442_0]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h0, h1, h1393, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h1435, hlam, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h2, hlam, p1442_0]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h0, h1437, hc12, hc45, hlam, hphi, ht23, ht34, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h1434, hlam, p1442_0]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [hlam, p1442_0]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h1437, hlam, p1442_0]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h1432, hc01, hc25, hlam, hphi, ht12, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h0, h1432, hc12, hc25, hlam, hphi, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h1435, hc03, hc35, hlam, hphi, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [h0, h1393, h1437, hc12, hc45, hlam, hphi, ht23, ht34, p1442_1]
                  · have p1442_0 := h1442c.1
                    have p1442_1 := h1442c.2.1
                    have p1442_2 := h1442c.2.2.1
                    have p1442_3 := h1442c.2.2.2
                    linarith only [hlam, p1442_0]
                · linarith only [h0, h1, h1307, h1434, h1441, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1469 | h1469
          · linarith only [h1, h1469, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1471 | h1471
            · linarith only [h1471, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1473 | h1473
              · linarith only [h0, h1307, h1473, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1475 | h1475
                · rcases h0bigk with h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [hlam, p1476_0]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h3, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h3, hlam, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h0, hlam, p1476_0]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [hlam, p1476_0]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h1307, hlam, p1476_0]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h1393, hlam, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h1432, hlam, p1476_0]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h1, hlam, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h0, h1, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [hlam, p1476_0]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h1434, hlam, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h1469, hlam, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h2, hlam, p1476_0]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h0, h2, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h1434, h1475, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [hlam, p1476_0]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h1471, hlam, p1476_0]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h1471, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h0, h1471, hc12, hc45, hlam, hphi, ht23, ht34, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h0, h1307, h1471, hc12, hc45, hlam, hphi, ht23, ht34, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [h1471, hc04, hc45, hlam, hphi, p1476_1]
                  · have p1476_0 := h1476c.1
                    have p1476_1 := h1476c.2.1
                    have p1476_2 := h1476c.2.2.1
                    have p1476_3 := h1476c.2.2.2
                    linarith only [hlam, p1476_0]
                · rcases h0bigk with h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [hlam, p1502_0]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h0, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h0, h1307, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h0, h1307, h1434, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h3, hlam, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h0, hlam, p1502_0]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [hlam, p1502_0]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h1307, hlam, p1502_0]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h1393, hlam, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h1432, hlam, p1502_0]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h1, hlam, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h0, h1, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [hlam, p1502_0]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h1434, hlam, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h1469, hlam, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h2, hlam, p1502_0]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h0, h2, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h2, h3, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [hlam, p1502_0]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h1471, hlam, p1502_0]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h1471, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h0, h1471, hc12, hc45, hlam, hphi, ht23, ht34, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h1, h1471, h1473, hc12, hc45, hlam, hphi, ht23, ht34, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [h1471, hc04, hc45, hlam, hphi, p1502_1]
                  · have p1502_0 := h1502c.1
                    have p1502_1 := h1502c.2.1
                    have p1502_2 := h1502c.2.2.1
                    have p1502_3 := h1502c.2.2.2
                    linarith only [hlam, p1502_0]

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3

end R2N4
