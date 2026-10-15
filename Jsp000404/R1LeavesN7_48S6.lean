import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_48S4
import Jsp000404.R1LeavesN7_48S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h10 h11
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h10 h11

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h10 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 4 (by decide) (by decide) with h1275 | h1275
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1276 | h1276
    · linarith only [h10, h1276, h8, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1278 | h1278
      · linarith only [h10, h1275, h1278, h8, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1280 | h1280
        · linarith only [h0, h10, h1280, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1275, h1276, h1280, hc23, hc35, hlam, hphi]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1283 | h1283
    · linarith only [h10, h1275, h1283, h9, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1285 | h1285
      · linarith only [h10, h1285, h9, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1287 | h1287
        · linarith only [h0, h10, h1275, h1287, h4, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1289 | h1289
          · linarith only [h10, h1283, h1289, h8, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1291 | h1291
            · linarith only [h0, h10, h1291, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1293 | h1293
              · linarith only [h0, h10, h1287, h1291, h1293, h2, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases h2bigk with h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  rcases p1295_3 (m.d 0 2) (by simp) with h1297 | h1297
                  · rcases p1295_3 (m.d 1 2) (by simp) with h1298 | h1298
                    · linarith only [h0, h1298, hlam]
                    · rcases p1295_3 (m.d 2 3) (by simp) with h1300 | h1300
                      · linarith only [h1300, h2, hlam]
                      · rcases p1295_3 (m.d 2 4) (by simp) with h1302 | h1302
                        · linarith only [h1302, h3, hlam]
                        · rcases p1295_3 (m.d 2 5) (by simp) with h1304 | h1304
                          · linarith only [h1304, h4, hlam]
                          · linarith only [h10, h1304, hlam]
                  · linarith only [h0, h1297, hlam]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h10, h1287, h4, h9, hlam, p1295_2]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h10, h4, h9, hlam, p1295_2]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h10, h1287, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1295_1]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h0, hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h10, h1289, hc23, hc35, hlam, hphi, p1295_1]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h0, h10, h1287, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1295_1]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h10, hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h2, hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h8, hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h1287, hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h1289, hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h3, hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h9, hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h0, h10, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1295_1]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h1291, hlam, p1295_1]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h4, hlam, p1295_0]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1295_1]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  rcases p1295_3 (m.d 0 2) (by simp) with h1328 | h1328
                  · rcases p1295_3 (m.d 1 2) (by simp) with h1329 | h1329
                    · linarith only [h10, h1329, hlam]
                    · linarith only [h1329, h8, hlam]
                  · linarith only [h1328, h2, hlam]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  rcases p1295_3 (m.d 0 2) (by simp) with h1333 | h1333
                  · rcases p1295_3 (m.d 1 2) (by simp) with h1334 | h1334
                    · linarith only [h10, h1334, hlam]
                    · linarith only [h1334, h9, hlam]
                  · linarith only [h1333, h3, hlam]
                · have p1295_0 := h1295c.1
                  have p1295_1 := h1295c.2.1
                  have p1295_2 := h1295c.2.2.1
                  have p1295_3 := h1295c.2.2.2
                  linarith only [hlam, p1295_0]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h10
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9 h10

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 5 (by decide) (by decide) with h1339 | h1339
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1340 | h1340
    · linarith only [h1340, h8, h9, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1342 | h1342
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1343 | h1343
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1344 | h1344
          · linarith only [h0, h1340, h1342, h1344, h2, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1346 | h1346
            · linarith only [h0, h1344, h1346, h2, h5, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h1342, h1344, h1346, h2, h5, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h1342, h1343, h8, h9, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1350 | h1350
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1351 | h1351
          · linarith only [h0, h1351, h3, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1353 | h1353
            · linarith only [h0, h1342, h1351, h1353, h2, h5, h8, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1355 | h1355
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1356 | h1356
                · rcases h2bigk with h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    rcases p1357_3 (m.d 0 2) (by simp) with h1359 | h1359
                    · rcases p1357_3 (m.d 1 2) (by simp) with h1360 | h1360
                      · linarith only [h0, h1360, hlam]
                      · rcases p1357_3 (m.d 2 3) (by simp) with h1362 | h1362
                        · linarith only [h1362, h2, hlam]
                        · rcases p1357_3 (m.d 2 4) (by simp) with h1364 | h1364
                          · linarith only [h1364, h3, hlam]
                          · linarith only [h1364, h9, hlam]
                    · linarith only [h0, h1359, hlam]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h1351, h2, h5, h8, h9, hlam, p1357_2]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h0, h1339, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p1357_1]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h1339, h3, h9, hlam, p1357_2]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h0, hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h0, h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1357_1]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h9, hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h0, h3, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p1357_1]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h2, hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h8, hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h1351, hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h1353, hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h3, hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h0, h3, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1357_1]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    rcases p1357_3 (m.d 0 2) (by simp) with h1383 | h1383
                    · rcases p1357_3 (m.d 1 2) (by simp) with h1384 | h1384
                      · linarith only [h1384, h9, hlam]
                      · linarith only [h1384, h8, hlam]
                    · linarith only [h1383, h2, hlam]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    rcases p1357_3 (m.d 0 2) (by simp) with h1389 | h1389
                    · rcases p1357_3 (m.d 1 2) (by simp) with h1390 | h1390
                      · linarith only [h1390, h9, hlam]
                      · linarith only [h1339, h1390, hlam]
                    · linarith only [h1389, h4, hlam]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h4, hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h1339, hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h0, h1339, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1357_1]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [h1355, hlam, p1357_0]
                  · have p1357_0 := h1357c.1
                    have p1357_1 := h1357c.2.1
                    have p1357_2 := h1357c.2.2.1
                    have p1357_3 := h1357c.2.2.2
                    linarith only [hlam, p1357_0]
                · linarith only [h0, h1339, h1351, h1356, h2, h5, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h1339, h1350, h1353, h1355, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · linarith only [h1339, h1350, h9, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1402 | h1402
    · linarith only [h1402, h8, h9, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1404 | h1404
      · linarith only [h1339, h1404, h8, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1406 | h1406
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1407 | h1407
          · linarith only [h1339, h1402, h1407, h8, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1409 | h1409
            · linarith only [h1339, h1404, h1409, h8, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1411 | h1411
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1412 | h1412
                · rcases h2bigk with h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    rcases p1413_3 (m.d 0 2) (by simp) with h1415 | h1415
                    · rcases p1413_3 (m.d 1 2) (by simp) with h1416 | h1416
                      · linarith only [h0, h1416, hlam]
                      · rcases p1413_3 (m.d 2 3) (by simp) with h1418 | h1418
                        · linarith only [h1418, h2, hlam]
                        · rcases p1413_3 (m.d 2 4) (by simp) with h1420 | h1420
                          · linarith only [h1420, h3, hlam]
                          · linarith only [h1420, h9, hlam]
                    · linarith only [h0, h1415, hlam]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h1339, h1407, h1411, h2, h5, h8, hlam, p1413_2]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h0, h1339, h1411, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1413_1]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h0, h1339, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1413_1]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h0, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h1339, h1407, h1411, hc23, hc34, hlam, hphi, p1413_1]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h9, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h1339, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h2, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h8, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h1407, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h1409, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h3, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h0, h3, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1413_1]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    rcases p1413_3 (m.d 0 2) (by simp) with h1439 | h1439
                    · rcases p1413_3 (m.d 1 2) (by simp) with h1440 | h1440
                      · linarith only [h1440, h9, hlam]
                      · linarith only [h1440, h8, hlam]
                    · linarith only [h1439, h2, hlam]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h0, h1339, h1407, h2, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1413_1]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h4, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h0, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1413_1]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    rcases p1413_3 (m.d 0 2) (by simp) with h1448 | h1448
                    · rcases p1413_3 (m.d 1 2) (by simp) with h1449 | h1449
                      · linarith only [h1339, h1449, hlam]
                      · linarith only [h1449, h8, hlam]
                    · linarith only [h1448, h2, hlam]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [h1411, hlam, p1413_0]
                  · have p1413_0 := h1413c.1
                    have p1413_1 := h1413c.2.1
                    have p1413_2 := h1413c.2.2.1
                    have p1413_3 := h1413c.2.2.2
                    linarith only [hlam, p1413_0]
                · linarith only [h0, h1407, h1412, h2, h5, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h1406, h1411, h8, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1457 | h1457
          · linarith only [h0, h1457, h3, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1459 | h1459
            · linarith only [h0, h1406, h1459, h2, h5, h7, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1461 | h1461
              · linarith only [h1406, h1457, h1461, h8, h9, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1461, h2, h5, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9
  · exact r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h9

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1464 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 5 (by decide) (by decide) with h1465 | h1465
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1466 | h1466
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1467 | h1467
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1468 | h1468
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1469 | h1469
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1470 | h1470
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1471 | h1471
              · linarith only [h0, h1464, h1471, h2, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h1464, h1468, h1471, h2, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1465, h1470, h2, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h1464, h1469, h2, h5, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1476 | h1476
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1477 | h1477
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1478 | h1478
              · linarith only [h1464, h1468, h1478, h8, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1480 | h1480
                · linarith only [h1464, h1468, h1476, h1480, hlam]
                · rcases h2bigk with h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c | h1482c
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [hlam, p1482_0]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    rcases p1482_3 (m.d 0 2) (by simp) with h1484 | h1484
                    · rcases p1482_3 (m.d 1 2) (by simp) with h1485 | h1485
                      · linarith only [h0, h1485, hlam]
                      · rcases p1482_3 (m.d 2 3) (by simp) with h1487 | h1487
                        · linarith only [h1487, h2, hlam]
                        · linarith only [h1487, h8, hlam]
                    · linarith only [h0, h1484, hlam]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h0, h1465, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p1482_1]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h1464, h2, h8, hlam, p1482_2]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h1465, h2, h8, hlam, p1482_2]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h0, hlam, p1482_0]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [hlam, p1482_0]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h8, hlam, p1482_0]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h1476, h2, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1482_1]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h0, h2, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p1482_1]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h2, hlam, p1482_0]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h0, h1464, h1476, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1482_1]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [hlam, p1482_0]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    rcases p1482_3 (m.d 0 2) (by simp) with h1502 | h1502
                    · rcases p1482_3 (m.d 1 2) (by simp) with h1503 | h1503
                      · linarith only [h1503, h8, hlam]
                      · linarith only [h1464, h1503, hlam]
                    · linarith only [h1502, h3, hlam]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    rcases p1482_3 (m.d 0 2) (by simp) with h1507 | h1507
                    · rcases p1482_3 (m.d 1 2) (by simp) with h1508 | h1508
                      · linarith only [h1508, h8, hlam]
                      · linarith only [h1465, h1508, hlam]
                    · linarith only [h1507, h4, hlam]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h3, hlam, p1482_0]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h1464, hlam, p1482_0]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h1476, hlam, p1482_1]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [hlam, p1482_0]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h1478, hlam, p1482_1]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h4, hlam, p1482_0]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h1465, hlam, p1482_0]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h1477, hlam, p1482_1]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [h0, h1465, h1476, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1482_1]
                  · have p1482_0 := h1482c.1
                    have p1482_1 := h1482c.2.1
                    have p1482_2 := h1482c.2.2.1
                    have p1482_3 := h1482c.2.2.2
                    linarith only [hlam, p1482_0]
            · linarith only [h0, h1465, h1477, h2, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h1464, h1476, h2, h5, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h1465, h1467, h8, hlam]
    · linarith only [h1464, h1466, h8, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1526 | h1526
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1527 | h1527
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1528 | h1528
        · linarith only [h1464, h1465, h1528, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1530 | h1530
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1531 | h1531
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1532 | h1532
              · linarith only [h1464, h1465, h1528, h1531, h1532, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1534 | h1534
                · linarith only [h1464, h1465, h1530, h1532, h1534, hlam]
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
                    rcases p1536_3 (m.d 0 2) (by simp) with h1538 | h1538
                    · rcases p1536_3 (m.d 1 2) (by simp) with h1539 | h1539
                      · linarith only [h0, h1539, hlam]
                      · rcases p1536_3 (m.d 2 3) (by simp) with h1541 | h1541
                        · linarith only [h1541, h2, hlam]
                        · linarith only [h1541, h8, hlam]
                    · linarith only [h0, h1538, hlam]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h0, h1464, h1530, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1536_1]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h1464, h1465, h4, hlam, p1536_2]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h0, h1464, h1465, h1530, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1536_1]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h0, hlam, p1536_0]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [hlam, p1536_0]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h8, hlam, p1536_0]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h1465, h1530, h1532, hc34, hc45, hlam, hphi, p1536_1]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h1465, hlam, p1536_0]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h2, hlam, p1536_0]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h0, h1464, h1530, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1536_1]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [hlam, p1536_0]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    rcases p1536_3 (m.d 0 2) (by simp) with h1556 | h1556
                    · rcases p1536_3 (m.d 1 2) (by simp) with h1557 | h1557
                      · linarith only [h1557, h8, hlam]
                      · linarith only [h1464, h1557, hlam]
                    · linarith only [h1556, h3, hlam]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h0, h1464, h1465, h1530, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1536_1]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h3, hlam, p1536_0]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h1464, hlam, p1536_0]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h1530, hlam, p1536_1]
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
                    linarith only [h4, hlam, p1536_0]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h0, h1464, h1530, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1536_1]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [h1531, hlam, p1536_1]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    rcases p1536_3 (m.d 0 2) (by simp) with h1570 | h1570
                    · rcases p1536_3 (m.d 1 2) (by simp) with h1571 | h1571
                      · linarith only [h1465, h1571, hlam]
                      · linarith only [h1464, h1571, hlam]
                    · linarith only [h1570, h3, hlam]
                  · have p1536_0 := h1536c.1
                    have p1536_1 := h1536c.2.1
                    have p1536_2 := h1536c.2.2.1
                    have p1536_3 := h1536c.2.2.2
                    linarith only [hlam, p1536_0]
            · linarith only [h0, h1464, h1530, h1531, h2, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h1464, h1530, h2, h5, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1578 | h1578
        · linarith only [h1464, h1465, h1578, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1580 | h1580
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1581 | h1581
            · linarith only [h0, h1464, h1527, h1580, h1581, h2, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1464, h1580, h1581, h2, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h1464, h1580, h2, h5, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h1464, h1526, h8, hlam]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_12_13_15_H_R_L_I_L_I_L_I_s7_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg7 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h8 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1464 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1586 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 4 (by decide) (by decide) with h1587 | h1587
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1588 | h1588
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1589 | h1589
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1590 | h1590
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1591 | h1591
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1592 | h1592
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1593 | h1593
              · rcases h2bigk with h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  rcases p1594_3 (m.d 0 2) (by simp) with h1596 | h1596
                  · rcases p1594_3 (m.d 1 2) (by simp) with h1597 | h1597
                    · linarith only [h0, h1597, hlam]
                    · rcases p1594_3 (m.d 2 3) (by simp) with h1599 | h1599
                      · linarith only [h1599, h2, hlam]
                      · linarith only [h1599, h8, hlam]
                  · linarith only [h0, h1596, hlam]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h0, h1586, h1591, h1593, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h0, h1464, h1586, h1591, h1593, hc01, hc45, hlam, hphi, ht0b, ht5b, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1464, h1586, h3, hlam, p1594_2]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h0, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h8, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1464, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h0, h1464, h3, hc01, hc25, hlam, hphi, ht0b, ht5b, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h2, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h0, h1586, h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h0, h1464, h1586, h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  rcases p1594_3 (m.d 0 2) (by simp) with h1615 | h1615
                  · rcases p1594_3 (m.d 1 2) (by simp) with h1616 | h1616
                    · linarith only [h1616, h8, hlam]
                    · linarith only [h1586, h1616, hlam]
                  · linarith only [h1615, h4, hlam]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h3, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h0, h1586, h1591, h1593, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1590, hlam, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  rcases p1594_3 (m.d 0 2) (by simp) with h1624 | h1624
                  · rcases p1594_3 (m.d 1 2) (by simp) with h1625 | h1625
                    · linarith only [h1464, h1625, hlam]
                    · linarith only [h1586, h1625, hlam]
                  · linarith only [h1624, h4, hlam]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h4, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1586, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1591, hlam, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1592, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [hlam, p1594_0]
              · linarith only [h0, h1586, h1592, h1593, h2, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1464, h1586, h1592, h2, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h1464, h1586, h1590, h1591, h2, h6, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h1586, h1590, h2, h5, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h1464, h1586, h1589, hlam]
    · linarith only [h1464, h1586, h1587, h1588, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1640 | h1640
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1641 | h1641
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1642 | h1642
        · linarith only [h0, h1587, h1640, h1642, h2, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h1586, h1642, h2, h5, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h1586, h1587, h1641, h8, hlam]
    · linarith only [h1586, h1640, h8, hlam]

end R2N4
