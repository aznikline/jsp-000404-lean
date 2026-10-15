import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_46S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h566 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h567 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h568 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h569 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h570 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
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
  have h0 := hg0
  rcases m.htr 3 4 5 (by decide) (by decide) with h1274 | h1274
  · linarith only [h1274, h568, h570, hlam]
  · rcases h0bigk with h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [hlam, p1276_0]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h0, hlam, p1276_1]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h451, hlam, p1276_0]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h451, h561, h562, h570, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1276_1]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h451, h558, h562, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1276_1, u2ehi3]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      rcases p1276_3 (m.d 0 1) (by simp) with h1282 | h1282
      · linarith only [h0, h1282, hlam]
      · rcases p1276_3 (m.d 0 2) (by simp) with h1284 | h1284
        · rcases p1276_3 (m.d 0 3) (by simp) with h1285 | h1285
          · linarith only [h1285, h556, hlam]
          · linarith only [h1285, h451, hlam]
        · linarith only [h0, h1284, hlam]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [hlam, p1276_0]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h0, h559, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1276_1, u3ehi3]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h0, h561, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1276_1, u2ehi3]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h0, h561, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1276_1, u2ehi3]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      rcases p1276_3 (m.d 0 1) (by simp) with h1293 | h1293
      · linarith only [h1293, h451, hlam]
      · rcases p1276_3 (m.d 0 2) (by simp) with h1295 | h1295
        · rcases p1276_3 (m.d 0 3) (by simp) with h1296 | h1296
          · rcases p1276_3 (m.d 0 4) (by simp) with h1297 | h1297
            · linarith only [h1297, h559, hlam]
            · linarith only [h0, h1297, h561, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
          · linarith only [h1296, h451, hlam]
        · linarith only [h0, h1295, hlam]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h556, hlam, p1276_1]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [hlam, p1276_0]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h561, h570, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1276_1, u2ehi3]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h451, h561, h562, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1276_1, u2ehi3]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      rcases p1276_3 (m.d 0 1) (by simp) with h1306 | h1306
      · linarith only [h1306, hlam, p1276_0]
      · rcases p1276_3 (m.d 0 2) (by simp) with h1308 | h1308
        · rcases p1276_3 (m.d 0 3) (by simp) with h1309 | h1309
          · rcases p1276_3 (m.d 0 4) (by simp) with h1310 | h1310
            · rcases p1276_3 (m.d 0 5) (by simp) with h1311 | h1311
              · linarith only [h1311, h561, hlam]
              · linarith only [h1311, h561, h570, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1276_1, u2ehi3]
            · linarith only [h1310, hlam, p1276_0]
          · linarith only [h1309, h451, hlam]
        · linarith only [h0, h1308, hlam]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h557, hlam, p1276_0]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h559, hlam, p1276_0]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [hlam, p1276_0]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h451, h559, h561, h562, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1276_1, u2ehi3]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      rcases p1276_3 (m.d 0 1) (by simp) with h1321 | h1321
      · linarith only [h1321, hlam, p1276_0]
      · rcases p1276_3 (m.d 0 2) (by simp) with h1323 | h1323
        · rcases p1276_3 (m.d 0 3) (by simp) with h1324 | h1324
          · rcases p1276_3 (m.d 0 4) (by simp) with h1325 | h1325
            · rcases p1276_3 (m.d 0 5) (by simp) with h1326 | h1326
              · rcases h0emin with h1327 | h1327 | h1327 | h1327 | h1327
                · linarith only [h1327, hc05, hlam, p1276_1]
                · rcases h3bigk with h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h451, hlam, p1329_1]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1329_1, u3ehi3]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    rcases p1329_3 (m.d 0 3) (by simp) with h1333 | h1333
                    · rcases p1329_3 (m.d 1 3) (by simp) with h1334 | h1334
                      · rcases p1329_3 (m.d 2 3) (by simp) with h1335 | h1335
                        · linarith only [h1335, h556, hlam]
                        · linarith only [h1335, h568, hlam]
                      · linarith only [h1334, h565, hlam]
                    · linarith only [h1333, hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    rcases p1329_3 (m.d 0 3) (by simp) with h1340 | h1340
                    · rcases p1329_3 (m.d 1 3) (by simp) with h1341 | h1341
                      · rcases p1329_3 (m.d 2 3) (by simp) with h1342 | h1342
                        · linarith only [h1342, h556, hlam]
                        · linarith only [h1342, h569, hlam]
                      · linarith only [h1341, h566, hlam]
                    · linarith only [h1340, hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h559, h561, h562, hc01, hc12, hlam, hphi, p1276_1, p1329_1]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h1274, h562, h569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1329_1, u3ehi3]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    rcases p1329_3 (m.d 0 3) (by simp) with h1350 | h1350
                    · linarith only [h1350, h451, hlam]
                    · linarith only [h1350, h559, hlam]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    rcases p1329_3 (m.d 0 3) (by simp) with h1353 | h1353
                    · linarith only [h1353, h451, hlam]
                    · linarith only [h1353, h560, hlam]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h556, hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h562, hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1329_1, u3ehi3]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h0, h1274, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1329_1, u3ehi3]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h559, hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h565, hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h568, hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h1274, hlam, p1329_1]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h560, hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h566, hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [h569, hlam, p1329_0]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [hc35, hlam, hphi, p1329_1, u3ehi3]
                  · have p1329_0 := h1329c.1
                    have p1329_1 := h1329c.2.1
                    have p1329_2 := h1329c.2.2.1
                    have p1329_3 := h1329c.2.2.2
                    linarith only [hlam, p1329_0]
                · rcases h3bigk with h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c | h1371c
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h451, hlam, p1371_1]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h451, h562, h569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1371_1, u3ehi4]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    rcases p1371_3 (m.d 0 3) (by simp) with h1375 | h1375
                    · rcases p1371_3 (m.d 1 3) (by simp) with h1376 | h1376
                      · rcases p1371_3 (m.d 2 3) (by simp) with h1377 | h1377
                        · linarith only [h1377, h556, hlam]
                        · linarith only [h1377, h568, hlam]
                      · linarith only [h1376, h565, hlam]
                    · linarith only [h1375, hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    rcases p1371_3 (m.d 0 3) (by simp) with h1382 | h1382
                    · rcases p1371_3 (m.d 1 3) (by simp) with h1383 | h1383
                      · rcases p1371_3 (m.d 2 3) (by simp) with h1384 | h1384
                        · linarith only [h1384, h556, hlam]
                        · linarith only [h1384, h569, hlam]
                      · linarith only [h1383, h566, hlam]
                    · linarith only [h1382, hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h1327, h562, hc12, hlam, ht01, p1371_1]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h1274, h562, h569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1371_1, u3ehi3]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    rcases p1371_3 (m.d 0 3) (by simp) with h1392 | h1392
                    · linarith only [h1392, h451, hlam]
                    · linarith only [h1392, h559, hlam]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    rcases p1371_3 (m.d 0 3) (by simp) with h1395 | h1395
                    · linarith only [h1395, h451, hlam]
                    · linarith only [h1395, h560, hlam]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h556, hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h562, hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1371_1, u3ehi3]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h0, h1274, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1371_1, u3ehi3]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h559, hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h565, hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h568, hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h1274, hlam, p1371_1]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h560, hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h566, hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [h569, hlam, p1371_0]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [hc35, hlam, hphi, p1371_1, u3ehi3]
                  · have p1371_0 := h1371c.1
                    have p1371_1 := h1371c.2.1
                    have p1371_2 := h1371c.2.2.1
                    have p1371_3 := h1371c.2.2.2
                    linarith only [hlam, p1371_0]
                · rcases h3bigk with h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h451, hlam, p1413_1]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi3]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    rcases p1413_3 (m.d 0 3) (by simp) with h1417 | h1417
                    · rcases p1413_3 (m.d 1 3) (by simp) with h1418 | h1418
                      · rcases p1413_3 (m.d 2 3) (by simp) with h1419 | h1419
                        · linarith only [h1419, h556, hlam]
                        · linarith only [h1419, h568, hlam]
                      · linarith only [h1418, h565, hlam]
                    · linarith only [h1417, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    rcases p1413_3 (m.d 0 3) (by simp) with h1424 | h1424
                    · rcases p1413_3 (m.d 1 3) (by simp) with h1425 | h1425
                      · rcases p1413_3 (m.d 2 3) (by simp) with h1426 | h1426
                        · linarith only [h1426, h556, hlam]
                        · linarith only [h1426, h569, hlam]
                      · linarith only [h1425, h566, hlam]
                    · linarith only [h1424, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h556, h562, h569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi4]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h562, h569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi4]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    rcases p1413_3 (m.d 0 3) (by simp) with h1434 | h1434
                    · linarith only [h1434, h451, hlam]
                    · linarith only [h1434, h559, hlam]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    rcases p1413_3 (m.d 0 3) (by simp) with h1437 | h1437
                    · linarith only [h1437, h451, hlam]
                    · linarith only [h1437, h560, hlam]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h556, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h562, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi3]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h0, h1274, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1413_1, u3ehi3]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h559, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h565, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h568, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h1274, hlam, p1413_1]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h560, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h566, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h569, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [hc35, hlam, hphi, p1413_1, u3ehi3]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [hlam, p1413_0]
                · rcases h3bigk with h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h451, hlam, p1455_1]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h451, h562, h569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1455_1, u3ehi4]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    rcases p1455_3 (m.d 0 3) (by simp) with h1459 | h1459
                    · rcases p1455_3 (m.d 1 3) (by simp) with h1460 | h1460
                      · rcases p1455_3 (m.d 2 3) (by simp) with h1461 | h1461
                        · linarith only [h1461, h556, hlam]
                        · linarith only [h1461, h568, hlam]
                      · linarith only [h1460, h565, hlam]
                    · linarith only [h1459, hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    rcases p1455_3 (m.d 0 3) (by simp) with h1466 | h1466
                    · rcases p1455_3 (m.d 1 3) (by simp) with h1467 | h1467
                      · rcases p1455_3 (m.d 2 3) (by simp) with h1468 | h1468
                        · linarith only [h1468, h556, hlam]
                        · linarith only [h1468, h569, hlam]
                      · linarith only [h1467, h566, hlam]
                    · linarith only [h1466, hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h1274, h556, h562, h569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1455_1, u3ehi3]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h1274, h562, h569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1455_1, u3ehi3]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    rcases p1455_3 (m.d 0 3) (by simp) with h1476 | h1476
                    · linarith only [h1476, h451, hlam]
                    · linarith only [h1476, h559, hlam]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    rcases p1455_3 (m.d 0 3) (by simp) with h1479 | h1479
                    · linarith only [h1479, h451, hlam]
                    · linarith only [h1479, h560, hlam]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h556, hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h562, hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h0, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1455_1, u3ehi3]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h0, h1274, h556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1455_1, u3ehi3]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h559, hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h565, hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h568, hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h1274, hlam, p1455_1]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h560, hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h566, hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [h569, hlam, p1455_0]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [hc35, hlam, hphi, p1455_1, u3ehi3]
                  · have p1455_0 := h1455c.1
                    have p1455_1 := h1455c.2.1
                    have p1455_2 := h1455c.2.2.1
                    have p1455_3 := h1455c.2.2.2
                    linarith only [hlam, p1455_0]
              · linarith only [h1326, hlam, p1276_0]
            · linarith only [h0, h1325, h561, h570, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
          · linarith only [h1324, h451, hlam]
        · linarith only [h0, h1323, hlam]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h558, hlam, p1276_1]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h560, hlam, p1276_0]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [h561, hlam, p1276_1]
    · have p1276_0 := h1276c.1
      have p1276_1 := h1276c.2.1
      have p1276_2 := h1276c.2.2.1
      have p1276_3 := h1276c.2.2.2
      linarith only [hlam, p1276_0]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h566 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h567 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h568 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h569 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
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
  have h0 := hg0
  rcases m.htr 2 4 5 (by decide) (by decide) with h570 | h570
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565 h566 h567 h568 h569 h570
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565 h566 h567 h568 h569 h570

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h566 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h567 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h568 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h569 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
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
  have h0 := hg0
  linarith only [h451, h560, h562, h568, h569, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h566 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h567 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h568 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
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
  have h0 := hg0
  rcases m.htr 2 3 5 (by decide) (by decide) with h569 | h569
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565 h566 h567 h568 h569
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565 h566 h567 h568 h569

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h566 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h567 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h568 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
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
  have h0 := hg0
  rcases m.htr 2 3 5 (by decide) (by decide) with h1506 | h1506
  · linarith only [h1506, h568, hc34, hlam, hphi, u3ehi4]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1508 | h1508
    · rcases m.htr 3 4 5 (by decide) (by decide) with h1509 | h1509
      · rcases h0bigk with h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c | h1510c
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [hlam, p1510_0]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h0, hlam, p1510_1]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h451, hlam, p1510_0]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h1506, h451, h560, h561, h562, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1510_1, u3ehi2]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h1506, h451, h560, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1510_1, u2ehi2]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          rcases p1510_3 (m.d 0 1) (by simp) with h1516 | h1516
          · linarith only [h0, h1516, hlam]
          · rcases p1510_3 (m.d 0 2) (by simp) with h1518 | h1518
            · rcases p1510_3 (m.d 0 3) (by simp) with h1519 | h1519
              · linarith only [h1519, h556, hlam]
              · linarith only [h1519, h451, hlam]
            · linarith only [h0, h1518, hlam]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [hlam, p1510_0]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h0, h1506, h1509, h559, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1510_1, u2ehi2]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h0, h1506, h560, h561, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1510_1, u2ehi2]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h0, h1506, h560, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1510_1, u2ehi2]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          rcases p1510_3 (m.d 0 1) (by simp) with h1527 | h1527
          · linarith only [h1527, h451, hlam]
          · rcases p1510_3 (m.d 0 2) (by simp) with h1529 | h1529
            · rcases p1510_3 (m.d 0 3) (by simp) with h1530 | h1530
              · rcases p1510_3 (m.d 0 4) (by simp) with h1531 | h1531
                · linarith only [h1531, h559, hlam]
                · linarith only [h1506, h1531, h560, h561, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1510_1, u2ehi2]
              · linarith only [h1530, h451, hlam]
            · linarith only [h0, h1529, hlam]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h556, hlam, p1510_1]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [hlam, p1510_0]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h1506, h451, h560, h561, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1510_1, u2ehi2]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h1506, h451, h560, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1510_1, u2ehi2]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          rcases p1510_3 (m.d 0 1) (by simp) with h1540 | h1540
          · linarith only [h1540, hlam, p1510_0]
          · rcases p1510_3 (m.d 0 2) (by simp) with h1542 | h1542
            · rcases p1510_3 (m.d 0 3) (by simp) with h1543 | h1543
              · rcases p1510_3 (m.d 0 4) (by simp) with h1544 | h1544
                · rcases p1510_3 (m.d 0 5) (by simp) with h1545 | h1545
                  · linarith only [h1545, h561, hlam]
                  · linarith only [h1506, h1545, h560, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1510_1, u2ehi2]
                · linarith only [h1544, hlam, p1510_0]
              · linarith only [h1543, h451, hlam]
            · linarith only [h0, h1542, hlam]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h557, hlam, p1510_0]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h559, hlam, p1510_0]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [hlam, p1510_0]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h1506, h560, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1510_1, u2ehi2]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          rcases p1510_3 (m.d 0 1) (by simp) with h1555 | h1555
          · linarith only [h1555, hlam, p1510_0]
          · rcases p1510_3 (m.d 0 2) (by simp) with h1557 | h1557
            · rcases p1510_3 (m.d 0 3) (by simp) with h1558 | h1558
              · rcases p1510_3 (m.d 0 4) (by simp) with h1559 | h1559
                · rcases p1510_3 (m.d 0 5) (by simp) with h1560 | h1560
                  · rcases h0emin with h1561 | h1561 | h1561 | h1561 | h1561
                    · linarith only [h1561, hc05, hlam, p1510_1]
                    · rcases h3bigk with h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c | h1563c
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h451, hlam, p1563_1]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        rcases p1563_3 (m.d 0 3) (by simp) with h1566 | h1566
                        · rcases p1563_3 (m.d 1 3) (by simp) with h1567 | h1567
                          · rcases p1563_3 (m.d 2 3) (by simp) with h1568 | h1568
                            · linarith only [h1568, h556, hlam]
                            · rcases p1563_3 (m.d 3 4) (by simp) with h1570 | h1570
                              · linarith only [h1570, h559, hlam]
                              · linarith only [h1570, h568, hlam]
                          · linarith only [h1567, h562, hlam]
                        · linarith only [h1566, h556, hlam]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h1506, h1509, h451, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1563_1, u2ehi2]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h1506, h451, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1563_1, u2ehi2]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h559, h561, h562, hc01, hc12, hlam, hphi, p1510_1, p1563_1]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        rcases p1563_3 (m.d 0 3) (by simp) with h1579 | h1579
                        · linarith only [h1579, h451, hlam]
                        · linarith only [h1579, h556, hlam]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h1506, h1509, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1563_1, u2ehi2]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h1506, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1563_1, u2ehi2]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h556, hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h562, hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h568, hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h1506, hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h559, hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h565, hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h559, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1563_1, u2ehi2]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h1506, h451, h559, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1563_1, u2ehi2]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h560, hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h566, hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [hc35, hlam, hphi, ht23, p1563_1, u2ehi2]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [h1509, hlam, p1563_0]
                      · have p1563_0 := h1563c.1
                        have p1563_1 := h1563c.2.1
                        have p1563_2 := h1563c.2.2.1
                        have p1563_3 := h1563c.2.2.2
                        linarith only [hlam, p1563_0]
                    · rcases h3bigk with h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c | h1599c
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h451, hlam, p1599_1]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        rcases p1599_3 (m.d 0 3) (by simp) with h1602 | h1602
                        · rcases p1599_3 (m.d 1 3) (by simp) with h1603 | h1603
                          · rcases p1599_3 (m.d 2 3) (by simp) with h1604 | h1604
                            · linarith only [h1604, h556, hlam]
                            · rcases p1599_3 (m.d 3 4) (by simp) with h1606 | h1606
                              · linarith only [h1606, h559, hlam]
                              · linarith only [h1606, h568, hlam]
                          · linarith only [h1603, h562, hlam]
                        · linarith only [h1602, h556, hlam]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1599_1, u2ehi2]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h1506, h451, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1599_1, u2ehi2]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h1561, h562, hc12, hlam, ht01, p1599_1]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        rcases p1599_3 (m.d 0 3) (by simp) with h1615 | h1615
                        · linarith only [h1615, h451, hlam]
                        · linarith only [h1615, h556, hlam]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h1506, h1509, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1599_1, u2ehi2]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h1506, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1599_1, u2ehi2]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h556, hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h562, hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h568, hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h1506, hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h559, hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h565, hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h559, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1599_1, u2ehi2]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h1506, h451, h559, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1599_1, u2ehi2]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h560, hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h566, hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [hc35, hlam, hphi, ht23, p1599_1, u2ehi2]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [h1509, hlam, p1599_0]
                      · have p1599_0 := h1599c.1
                        have p1599_1 := h1599c.2.1
                        have p1599_2 := h1599c.2.2.1
                        have p1599_3 := h1599c.2.2.2
                        linarith only [hlam, p1599_0]
                    · rcases h3bigk with h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h451, hlam, p1635_1]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        rcases p1635_3 (m.d 0 3) (by simp) with h1638 | h1638
                        · rcases p1635_3 (m.d 1 3) (by simp) with h1639 | h1639
                          · rcases p1635_3 (m.d 2 3) (by simp) with h1640 | h1640
                            · linarith only [h1640, h556, hlam]
                            · rcases p1635_3 (m.d 3 4) (by simp) with h1642 | h1642
                              · linarith only [h1642, h559, hlam]
                              · linarith only [h1642, h568, hlam]
                          · linarith only [h1639, h562, hlam]
                        · linarith only [h1638, h556, hlam]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1635_1, u2ehi2]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1506, h451, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1635_1, u2ehi2]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h559, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1635_1, u2ehi2]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        rcases p1635_3 (m.d 0 3) (by simp) with h1651 | h1651
                        · linarith only [h1651, h451, hlam]
                        · linarith only [h1651, h556, hlam]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1506, h1509, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1635_1, u2ehi2]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1506, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1635_1, u2ehi2]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h556, hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h562, hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h568, hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1506, hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h559, hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h565, hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h559, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1635_1, u2ehi2]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1506, h451, h559, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1635_1, u2ehi2]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h560, hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h566, hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [hc35, hlam, hphi, ht23, p1635_1, u2ehi2]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [h1509, hlam, p1635_0]
                      · have p1635_0 := h1635c.1
                        have p1635_1 := h1635c.2.1
                        have p1635_2 := h1635c.2.2.1
                        have p1635_3 := h1635c.2.2.2
                        linarith only [hlam, p1635_0]
                    · rcases h3bigk with h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c | h1671c
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h451, hlam, p1671_1]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        rcases p1671_3 (m.d 0 3) (by simp) with h1674 | h1674
                        · rcases p1671_3 (m.d 1 3) (by simp) with h1675 | h1675
                          · rcases p1671_3 (m.d 2 3) (by simp) with h1676 | h1676
                            · linarith only [h1676, h556, hlam]
                            · rcases p1671_3 (m.d 3 4) (by simp) with h1678 | h1678
                              · linarith only [h1678, h559, hlam]
                              · linarith only [h1678, h568, hlam]
                          · linarith only [h1675, h562, hlam]
                        · linarith only [h1674, h556, hlam]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h451, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi2]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1506, h451, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi2]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h559, h562, h568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi2]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        rcases p1671_3 (m.d 0 3) (by simp) with h1687 | h1687
                        · linarith only [h1687, h451, hlam]
                        · linarith only [h1687, h556, hlam]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1506, h1509, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi2]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1506, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi2]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h556, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h562, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h568, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1506, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h559, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h565, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h559, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi2]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1506, h451, h559, h562, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1671_1, u2ehi2]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h560, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h566, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [hc35, hlam, hphi, ht23, p1671_1, u2ehi2]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [h1509, hlam, p1671_0]
                      · have p1671_0 := h1671c.1
                        have p1671_1 := h1671c.2.1
                        have p1671_2 := h1671c.2.2.1
                        have p1671_3 := h1671c.2.2.2
                        linarith only [hlam, p1671_0]
                  · linarith only [h1560, hlam, p1510_0]
                · linarith only [h1559, h561, hlam, p1510_1]
              · linarith only [h1558, h451, hlam]
            · linarith only [h0, h1557, hlam]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h558, hlam, p1510_1]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h560, hlam, p1510_0]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [h561, hlam, p1510_1]
        · have p1510_0 := h1510c.1
          have p1510_1 := h1510c.2.1
          have p1510_2 := h1510c.2.2.1
          have p1510_3 := h1510c.2.2.2
          linarith only [hlam, p1510_0]
      · linarith only [h1509, h559, h561, h568, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h1716 | h1716
      · linarith only [h0, h1508, h1716, h556, h559, h568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
      · linarith only [h1716, h568, hc45, hlam, hphi, ht23, ht34, u2ehi2]

set_option maxHeartbeats 5094000 in
theorem r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h451 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h556 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h557 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h558 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h559 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h560 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h561 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h562 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h563 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h564 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h565 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h566 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h567 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
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
  have h0 := hg0
  rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565 h566 h567 h568
  · exact r1l7_10_12_23_L_I_L_R_M_IR_s0_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h451 h556 h557 h558 h559 h560 h561 h562 h563 h564 h565 h566 h567 h568

end R2N4
