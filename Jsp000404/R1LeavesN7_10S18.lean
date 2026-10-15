import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S15
import Jsp000404.R1LeavesN7_10S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h10681 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 2 3 (by decide) (by decide) with h11478 | h11478
  · rcases m.htr 1 2 4 (by decide) (by decide) with h11479 | h11479
    · rcases m.htr 1 2 5 (by decide) (by decide) with h11480 | h11480
      · rcases m.htr 1 3 4 (by decide) (by decide) with h11481 | h11481
        · rcases m.htr 1 4 5 (by decide) (by decide) with h11482 | h11482
          · rcases m.htr 2 3 4 (by decide) (by decide) with h11483 | h11483
            · linarith only [h11483, h8886, h8889, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11485 | h11485
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11486 | h11486
                · linarith only [h10681, h11486, h8887, hlam]
                · linarith only [h11483, h11485, h11486, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11489 | h11489
                · linarith only [h0, h10681, h11489, h6874, h8887, hc01, hc12, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11491 | h11491
                  · linarith only [h10681, h11478, h11481, h11491, h6874, hc01, hc12, hlam, hphi]
                  · rcases h2bigk with h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c | h11493c
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h0, hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      rcases p11493_3 (m.d 0 2) (by simp) with h11496 | h11496
                      · rcases p11493_3 (m.d 1 2) (by simp) with h11497 | h11497
                        · rcases p11493_3 (m.d 2 3) (by simp) with h11498 | h11498
                          · linarith only [h11498, hlam, p11493_0]
                          · rcases p11493_3 (m.d 2 4) (by simp) with h11500 | h11500
                            · linarith only [h11500, h8887, hlam]
                            · linarith only [h11483, h11500, hlam]
                        · linarith only [h11478, h11497, hlam]
                      · linarith only [h11496, hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      rcases p11493_3 (m.d 0 2) (by simp) with h11505 | h11505
                      · rcases p11493_3 (m.d 1 2) (by simp) with h11506 | h11506
                        · rcases p11493_3 (m.d 2 3) (by simp) with h11507 | h11507
                          · linarith only [h11507, h8886, hlam]
                          · rcases p11493_3 (m.d 2 4) (by simp) with h11509 | h11509
                            · linarith only [h11509, hlam, p11493_0]
                            · rcases p11493_3 (m.d 2 5) (by simp) with h11511 | h11511
                              · linarith only [h11511, h8888, hlam]
                              · linarith only [h11489, h11511, hlam]
                        · linarith only [h11479, h11506, hlam]
                      · linarith only [h11505, hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      rcases p11493_3 (m.d 0 2) (by simp) with h11516 | h11516
                      · rcases p11493_3 (m.d 1 2) (by simp) with h11517 | h11517
                        · rcases p11493_3 (m.d 2 3) (by simp) with h11518 | h11518
                          · linarith only [h11518, h8886, hlam]
                          · rcases p11493_3 (m.d 2 4) (by simp) with h11520 | h11520
                            · linarith only [h11520, h8887, hlam]
                            · rcases p11493_3 (m.d 2 5) (by simp) with h11522 | h11522
                              · linarith only [h11522, hlam, p11493_0]
                              · rcases h4bigk with h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c | h11524c
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [hlam, p11524_0]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h6874, hlam, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11483, h8889, hc23, hc34, hlam, hphi, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h8889, hlam, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h10681, hlam, p11524_0]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11478, h11481, h6874, hc01, hc12, hlam, hphi, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [hlam, p11524_0]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  rcases p11524_3 (m.d 0 4) (by simp) with h11532 | h11532
                                  · linarith only [h11532, h6874, hlam]
                                  · linarith only [h11532, h8887, hlam]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11478, h11481, h8886, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h10681, h11478, h11481, h6874, hc01, hc12, hlam, hphi, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h8887, hlam, p11524_0]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11479, hlam, p11524_0]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [hlam, p11524_0]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11483, hlam, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11489, hlam, p11524_0]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11481, hlam, p11524_0]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11478, h11481, h11483, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [hlam, p11524_0]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11491, hlam, p11524_0]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11482, hlam, p11524_0]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11478, h11481, h11482, h11483, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [h11478, h11481, h11482, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11524_1]
                                · have p11524_0 := h11524c.1
                                  have p11524_1 := h11524c.2.1
                                  have p11524_2 := h11524c.2.2.1
                                  have p11524_3 := h11524c.2.2.2
                                  linarith only [hlam, p11524_0]
                        · linarith only [h11480, h11517, hlam]
                      · linarith only [h11516, hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      rcases p11493_3 (m.d 0 2) (by simp) with h11554 | h11554
                      · linarith only [h0, h11554, hlam]
                      · rcases p11493_3 (m.d 1 2) (by simp) with h11556 | h11556
                        · rcases p11493_3 (m.d 2 3) (by simp) with h11557 | h11557
                          · linarith only [h11478, h11557, hlam]
                          · rcases p11493_3 (m.d 2 4) (by simp) with h11559 | h11559
                            · linarith only [h11479, h11559, hlam]
                            · rcases p11493_3 (m.d 2 5) (by simp) with h11561 | h11561
                              · linarith only [h11480, h11561, hlam]
                              · rcases h4bigk with h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c | h11563c
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [hlam, p11563_0]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h6874, hlam, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11483, h8887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11493_1, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h8889, hlam, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h10681, hlam, p11563_0]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11478, h11481, h6874, hc01, hc12, hlam, hphi, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [hlam, p11563_0]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  rcases p11563_3 (m.d 0 4) (by simp) with h11571 | h11571
                                  · linarith only [h11571, h6874, hlam]
                                  · linarith only [h11571, h8887, hlam]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11478, h11481, h8886, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h10681, h11478, h11481, h6874, hc01, hc12, hlam, hphi, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h8887, hlam, p11563_0]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11479, hlam, p11563_0]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [hlam, p11563_0]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11483, hlam, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11489, hlam, p11563_0]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11481, hlam, p11563_0]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11478, h11481, h11483, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [hlam, p11563_0]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11491, hlam, p11563_0]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11482, hlam, p11563_0]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11478, h11481, h11482, h11483, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [h11478, h11481, h11482, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11563_1]
                                · have p11563_0 := h11563c.1
                                  have p11563_1 := h11563c.2.1
                                  have p11563_2 := h11563c.2.2.1
                                  have p11563_3 := h11563c.2.2.2
                                  linarith only [hlam, p11563_0]
                        · linarith only [h0, h11556, hlam]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h11478, h11481, h11482, h11491, h8886, h8889, hlam, p11493_2]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      rcases p11493_3 (m.d 0 2) (by simp) with h11594 | h11594
                      · linarith only [h0, h11594, hlam]
                      · linarith only [h11594, h8887, hlam]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      rcases p11493_3 (m.d 0 2) (by simp) with h11597 | h11597
                      · linarith only [h0, h11597, hlam]
                      · linarith only [h11597, h8888, hlam]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h8886, hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h11478, hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h11483, hlam, p11493_1]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h11485, hlam, p11493_1]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h8887, hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h11479, hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h11478, h11481, h11482, h11491, h8887, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11493_1]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h11489, hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h8888, hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [h11480, hlam, p11493_0]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      rcases p11493_3 (m.d 0 2) (by simp) with h11612 | h11612
                      · rcases p11493_3 (m.d 1 2) (by simp) with h11613 | h11613
                        · rcases p11493_3 (m.d 2 3) (by simp) with h11614 | h11614
                          · linarith only [h11485, h11614, hlam]
                          · rcases p11493_3 (m.d 2 4) (by simp) with h11616 | h11616
                            · linarith only [h11489, h11616, hlam]
                            · linarith only [h11483, h11616, hlam]
                        · linarith only [h11478, h11613, hlam]
                      · linarith only [h11612, h8886, hlam]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      rcases p11493_3 (m.d 0 2) (by simp) with h11621 | h11621
                      · rcases p11493_3 (m.d 1 2) (by simp) with h11622 | h11622
                        · rcases p11493_3 (m.d 2 3) (by simp) with h11623 | h11623
                          · linarith only [h11485, h11623, hlam]
                          · rcases p11493_3 (m.d 2 4) (by simp) with h11625 | h11625
                            · linarith only [h11489, h11625, hlam]
                            · rcases p11493_3 (m.d 2 5) (by simp) with h11627 | h11627
                              · rcases h4bigk with h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c | h11628c
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [hlam, p11628_0]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h6874, hlam, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11478, h11481, h11482, h11483, h11491, h8889, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h8889, hlam, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h10681, hlam, p11628_0]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11478, h11481, h6874, hc01, hc12, hlam, hphi, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [hlam, p11628_0]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  rcases p11628_3 (m.d 0 4) (by simp) with h11636 | h11636
                                  · linarith only [h11636, h6874, hlam]
                                  · linarith only [h11636, h8887, hlam]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11478, h11481, h8889, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h10681, h11478, h11481, h6874, hc01, hc12, hlam, hphi, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h8887, hlam, p11628_0]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11479, hlam, p11628_0]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [hlam, p11628_0]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11483, hlam, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11489, hlam, p11628_0]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11481, hlam, p11628_0]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11478, h11481, h11483, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [hlam, p11628_0]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11491, hlam, p11628_0]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11478, h11481, h11482, h6874, hc01, hc12, hlam, hphi, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11482, hlam, p11628_0]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11478, h11481, h11482, h11483, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [h11478, h11481, h11482, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11628_1]
                                · have p11628_0 := h11628c.1
                                  have p11628_1 := h11628c.2.1
                                  have p11628_2 := h11628c.2.2.1
                                  have p11628_3 := h11628c.2.2.2
                                  linarith only [hlam, p11628_0]
                              · linarith only [h11489, h11627, hlam]
                        · linarith only [h11479, h11622, hlam]
                      · linarith only [h11621, h8887, hlam]
                    · have p11493_0 := h11493c.1
                      have p11493_1 := h11493c.2.1
                      have p11493_2 := h11493c.2.2.1
                      have p11493_3 := h11493c.2.2.2
                      linarith only [hlam, p11493_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h11660 | h11660
            · linarith only [h11660, h8886, h8889, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11662 | h11662
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11663 | h11663
                · linarith only [h11481, h11482, h11662, h11663, h8886, h8889, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h11660, h11662, h11663, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11666 | h11666
                · linarith only [h11482, h11666, h6874, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11668 | h11668
                  · linarith only [h11481, h11482, h11668, hlam]
                  · rcases h2bigk with h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c | h11670c
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [h0, hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      rcases p11670_3 (m.d 0 2) (by simp) with h11673 | h11673
                      · rcases p11670_3 (m.d 1 2) (by simp) with h11674 | h11674
                        · rcases p11670_3 (m.d 2 3) (by simp) with h11675 | h11675
                          · linarith only [h11675, hlam, p11670_0]
                          · rcases p11670_3 (m.d 2 4) (by simp) with h11677 | h11677
                            · linarith only [h11677, h8887, hlam]
                            · linarith only [h11660, h11677, hlam]
                        · linarith only [h11478, h11674, hlam]
                      · linarith only [h11673, hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      rcases p11670_3 (m.d 0 2) (by simp) with h11682 | h11682
                      · rcases p11670_3 (m.d 1 2) (by simp) with h11683 | h11683
                        · rcases p11670_3 (m.d 2 3) (by simp) with h11684 | h11684
                          · linarith only [h11684, h8886, hlam]
                          · rcases p11670_3 (m.d 2 4) (by simp) with h11686 | h11686
                            · linarith only [h11686, hlam, p11670_0]
                            · rcases p11670_3 (m.d 2 5) (by simp) with h11688 | h11688
                              · linarith only [h11688, h8888, hlam]
                              · linarith only [h11666, h11688, hlam]
                        · linarith only [h11479, h11683, hlam]
                      · linarith only [h11682, hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      rcases p11670_3 (m.d 0 2) (by simp) with h11693 | h11693
                      · rcases p11670_3 (m.d 1 2) (by simp) with h11694 | h11694
                        · rcases p11670_3 (m.d 2 3) (by simp) with h11695 | h11695
                          · linarith only [h11695, h8886, hlam]
                          · rcases p11670_3 (m.d 2 4) (by simp) with h11697 | h11697
                            · linarith only [h11697, h8887, hlam]
                            · rcases p11670_3 (m.d 2 5) (by simp) with h11699 | h11699
                              · linarith only [h11699, hlam, p11670_0]
                              · rcases h4bigk with h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c | h11701c
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [hlam, p11701_0]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h6874, hlam, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11481, h11482, h8889, hc24, hc45, hlam, hphi, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h8889, hlam, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h10681, hlam, p11701_0]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11482, hc04, hc45, hlam, hphi, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [hlam, p11701_0]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11482, hc24, hc45, hlam, hphi, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11482, hc34, hc45, hlam, hphi, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11482, hlam, p11701_0]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h8887, hlam, p11701_0]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11479, hlam, p11701_0]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [hlam, p11701_0]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11660, hlam, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11666, hlam, p11701_0]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11481, hlam, p11701_0]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11481, h11482, hc24, hc45, hlam, hphi, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [hlam, p11701_0]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11668, hlam, p11701_0]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h11660, hc23, hc45, hlam, hphi, ht34, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [h8886, h8889, hc23, hc45, hlam, hphi, ht34, p11701_1]
                                · have p11701_0 := h11701c.1
                                  have p11701_1 := h11701c.2.1
                                  have p11701_2 := h11701c.2.2.1
                                  have p11701_3 := h11701c.2.2.2
                                  linarith only [hlam, p11701_0]
                        · linarith only [h11480, h11694, hlam]
                      · linarith only [h11693, hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      rcases p11670_3 (m.d 0 2) (by simp) with h11729 | h11729
                      · linarith only [h0, h11729, hlam]
                      · rcases p11670_3 (m.d 1 2) (by simp) with h11731 | h11731
                        · rcases p11670_3 (m.d 2 3) (by simp) with h11732 | h11732
                          · linarith only [h11478, h11732, hlam]
                          · rcases p11670_3 (m.d 2 4) (by simp) with h11734 | h11734
                            · linarith only [h11479, h11734, hlam]
                            · rcases p11670_3 (m.d 2 5) (by simp) with h11736 | h11736
                              · linarith only [h11480, h11736, hlam]
                              · rcases h4bigk with h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c | h11738c
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [hlam, p11738_0]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h6874, hlam, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h11660, h8887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11670_1, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h8889, hlam, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h10681, hlam, p11738_0]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h6874, hc01, hc14, hlam, hphi, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [hlam, p11738_0]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h11482, h11660, hc23, hc45, hlam, hphi, ht34, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h11482, h8886, h8889, hc23, hc45, hlam, hphi, ht34, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h11482, hlam, p11738_0]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h8887, hlam, p11738_0]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h11479, hlam, p11738_0]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [hlam, p11738_0]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h11660, hlam, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h11666, hlam, p11738_0]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h11481, hlam, p11738_0]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h11481, h11482, h11660, hc23, hc45, hlam, hphi, ht34, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [hlam, p11738_0]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h11668, hlam, p11738_0]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h11660, hc23, hc45, hlam, hphi, ht34, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [h8886, h8889, hc23, hc45, hlam, hphi, ht34, p11738_1]
                                · have p11738_0 := h11738c.1
                                  have p11738_1 := h11738c.2.1
                                  have p11738_2 := h11738c.2.2.1
                                  have p11738_3 := h11738c.2.2.2
                                  linarith only [hlam, p11738_0]
                        · linarith only [h0, h11731, hlam]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      rcases p11670_3 (m.d 0 2) (by simp) with h11766 | h11766
                      · linarith only [h0, h11766, hlam]
                      · linarith only [h11766, h8886, hlam]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      rcases p11670_3 (m.d 0 2) (by simp) with h11769 | h11769
                      · linarith only [h0, h11769, hlam]
                      · linarith only [h11769, h8887, hlam]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      rcases p11670_3 (m.d 0 2) (by simp) with h11772 | h11772
                      · linarith only [h0, h11772, hlam]
                      · linarith only [h11772, h8888, hlam]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [h8886, hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [h11478, hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [h11660, hlam, p11670_1]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [h11662, hlam, p11670_1]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [h8887, hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [h11479, hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [h10681, h8887, hc23, hc45, hlam, hphi, ht34, p11670_1]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [h11666, hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [h8888, hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [h11480, hlam, p11670_0]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      rcases p11670_3 (m.d 0 2) (by simp) with h11787 | h11787
                      · rcases p11670_3 (m.d 1 2) (by simp) with h11788 | h11788
                        · rcases p11670_3 (m.d 2 3) (by simp) with h11789 | h11789
                          · linarith only [h11662, h11789, hlam]
                          · rcases p11670_3 (m.d 2 4) (by simp) with h11791 | h11791
                            · linarith only [h11666, h11791, hlam]
                            · linarith only [h11660, h11791, hlam]
                        · linarith only [h11478, h11788, hlam]
                      · linarith only [h11787, h8886, hlam]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      rcases p11670_3 (m.d 0 2) (by simp) with h11796 | h11796
                      · rcases p11670_3 (m.d 1 2) (by simp) with h11797 | h11797
                        · rcases p11670_3 (m.d 2 3) (by simp) with h11798 | h11798
                          · linarith only [h11662, h11798, hlam]
                          · rcases p11670_3 (m.d 2 4) (by simp) with h11800 | h11800
                            · linarith only [h11666, h11800, hlam]
                            · rcases p11670_3 (m.d 2 5) (by simp) with h11802 | h11802
                              · rcases h4bigk with h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c | h11803c
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [hlam, p11803_0]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h6874, hlam, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11481, h11482, h11660, h8889, hc23, hc45, hlam, hphi, ht34, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h8889, hlam, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h10681, hlam, p11803_0]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11482, hc04, hc45, hlam, hphi, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [hlam, p11803_0]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11482, h11660, hc23, hc45, hlam, hphi, ht34, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11482, hc34, hc45, hlam, hphi, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11482, hlam, p11803_0]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h8887, hlam, p11803_0]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11479, hlam, p11803_0]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [hlam, p11803_0]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11660, hlam, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11666, hlam, p11803_0]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h0, h11660, h6874, h8888, hc01, hc12, hc23, hc34, hlam, hphi, p11670_1, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11481, hlam, p11803_0]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11481, h11482, h11660, hc23, hc45, hlam, hphi, ht34, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [hlam, p11803_0]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11668, hlam, p11803_0]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h0, h11660, h6874, h8888, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p11670_1, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [hc14, hc45, hlam, hphi, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h11660, hc23, hc45, hlam, hphi, ht34, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [h8886, h8889, hc23, hc45, hlam, hphi, ht34, p11803_1]
                                · have p11803_0 := h11803c.1
                                  have p11803_1 := h11803c.2.1
                                  have p11803_2 := h11803c.2.2.1
                                  have p11803_3 := h11803c.2.2.2
                                  linarith only [hlam, p11803_0]
                              · linarith only [h11666, h11802, hlam]
                        · linarith only [h11479, h11797, hlam]
                      · linarith only [h11796, h8887, hlam]
                    · have p11670_0 := h11670c.1
                      have p11670_1 := h11670c.2.1
                      have p11670_2 := h11670c.2.2.1
                      have p11670_3 := h11670c.2.2.2
                      linarith only [hlam, p11670_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h11833 | h11833
          · rcases m.htr 2 3 4 (by decide) (by decide) with h11834 | h11834
            · linarith only [h11834, h8886, h8889, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11836 | h11836
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11837 | h11837
                · linarith only [h0, h10681, h11836, h11837, h8886, h8887, h8889, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h11834, h11836, h11837, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11840 | h11840
                · linarith only [h0, h10681, h11840, h6874, h8887, hc01, hc12, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11842 | h11842
                  · rcases h2bigk with h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c | h11843c
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h0, hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      rcases p11843_3 (m.d 0 2) (by simp) with h11846 | h11846
                      · rcases p11843_3 (m.d 1 2) (by simp) with h11847 | h11847
                        · rcases p11843_3 (m.d 2 3) (by simp) with h11848 | h11848
                          · linarith only [h11848, hlam, p11843_0]
                          · rcases p11843_3 (m.d 2 4) (by simp) with h11850 | h11850
                            · linarith only [h11850, h8887, hlam]
                            · linarith only [h11834, h11850, hlam]
                        · linarith only [h11478, h11847, hlam]
                      · linarith only [h11846, hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      rcases p11843_3 (m.d 0 2) (by simp) with h11855 | h11855
                      · rcases p11843_3 (m.d 1 2) (by simp) with h11856 | h11856
                        · rcases p11843_3 (m.d 2 3) (by simp) with h11857 | h11857
                          · linarith only [h11857, h8886, hlam]
                          · rcases p11843_3 (m.d 2 4) (by simp) with h11859 | h11859
                            · linarith only [h11859, hlam, p11843_0]
                            · rcases p11843_3 (m.d 2 5) (by simp) with h11861 | h11861
                              · linarith only [h11861, h8888, hlam]
                              · linarith only [h11840, h11861, hlam]
                        · linarith only [h11479, h11856, hlam]
                      · linarith only [h11855, hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      rcases p11843_3 (m.d 0 2) (by simp) with h11866 | h11866
                      · rcases p11843_3 (m.d 1 2) (by simp) with h11867 | h11867
                        · rcases p11843_3 (m.d 2 3) (by simp) with h11868 | h11868
                          · linarith only [h11868, h8886, hlam]
                          · rcases p11843_3 (m.d 2 4) (by simp) with h11870 | h11870
                            · linarith only [h11870, h8887, hlam]
                            · rcases p11843_3 (m.d 2 5) (by simp) with h11872 | h11872
                              · linarith only [h11872, hlam, p11843_0]
                              · rcases h4bigk with h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c | h11874c
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [hlam, p11874_0]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h6874, hlam, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h10681, h11833, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h8889, hlam, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h10681, hlam, p11874_0]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h6874, hc01, hc14, hlam, hphi, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [hlam, p11874_0]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h11481, h11834, hc23, hc34, hlam, hphi, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h11481, hlam, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h10681, h11481, h11834, h11840, h8888, hc23, hc34, hlam, hphi, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h8887, hlam, p11874_0]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h11479, hlam, p11874_0]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [hlam, p11874_0]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h11834, hlam, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h11840, hlam, p11874_0]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h11834, hc23, hc34, hlam, hphi, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [hlam, p11874_0]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h10681, h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h11833, h6874, hc01, hc14, hlam, hphi, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h11833, hlam, p11874_0]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h11481, h11833, h11834, hc23, hc34, hlam, hphi, p11874_1]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [h11842, hlam, p11874_0]
                                · have p11874_0 := h11874c.1
                                  have p11874_1 := h11874c.2.1
                                  have p11874_2 := h11874c.2.2.1
                                  have p11874_3 := h11874c.2.2.2
                                  linarith only [hlam, p11874_0]
                        · linarith only [h11480, h11867, hlam]
                      · linarith only [h11866, hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      rcases p11843_3 (m.d 0 2) (by simp) with h11902 | h11902
                      · linarith only [h0, h11902, hlam]
                      · rcases p11843_3 (m.d 1 2) (by simp) with h11904 | h11904
                        · rcases p11843_3 (m.d 2 3) (by simp) with h11905 | h11905
                          · linarith only [h11478, h11905, hlam]
                          · rcases p11843_3 (m.d 2 4) (by simp) with h11907 | h11907
                            · linarith only [h11479, h11907, hlam]
                            · rcases p11843_3 (m.d 2 5) (by simp) with h11909 | h11909
                              · linarith only [h11480, h11909, hlam]
                              · rcases h4bigk with h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c | h11911c
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [hlam, p11911_0]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h6874, hlam, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11481, h11834, h6874, hc23, hc34, hlam, hphi, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h8889, hlam, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h10681, hlam, p11911_0]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11481, h8889, hc03, hc34, hlam, hphi, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [hlam, p11911_0]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11481, h11834, hc23, hc34, hlam, hphi, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11481, hlam, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h10681, h11481, h11834, h11840, h6874, h8888, hc01, hc12, hc23, hc34, hlam, hphi, p11843_1, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h8887, hlam, p11911_0]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11479, hlam, p11911_0]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [hlam, p11911_0]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11834, hlam, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11840, hlam, p11911_0]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11834, h11840, h6874, h8888, hc01, hc12, hc23, hc34, hlam, hphi, p11843_1, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11834, h11840, h6874, h8888, hc01, hc12, hc23, hc34, hlam, hphi, p11843_1, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11834, hc23, hc34, hlam, hphi, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [hlam, p11911_0]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h10681, h11834, h11840, h6874, h8888, hc01, hc12, hc23, hc34, hlam, hphi, p11843_1, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11833, h6874, hc01, hc14, hlam, hphi, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11833, hlam, p11911_0]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11481, h11833, h11834, hc23, hc34, hlam, hphi, p11911_1]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [h11842, hlam, p11911_0]
                                · have p11911_0 := h11911c.1
                                  have p11911_1 := h11911c.2.1
                                  have p11911_2 := h11911c.2.2.1
                                  have p11911_3 := h11911c.2.2.2
                                  linarith only [hlam, p11911_0]
                        · linarith only [h0, h11904, hlam]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      rcases p11843_3 (m.d 0 2) (by simp) with h11939 | h11939
                      · linarith only [h0, h11939, hlam]
                      · linarith only [h11939, h8886, hlam]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      rcases p11843_3 (m.d 0 2) (by simp) with h11942 | h11942
                      · linarith only [h0, h11942, hlam]
                      · linarith only [h11942, h8887, hlam]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      rcases p11843_3 (m.d 0 2) (by simp) with h11945 | h11945
                      · linarith only [h0, h11945, hlam]
                      · linarith only [h11945, h8888, hlam]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h8886, hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h11478, hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h11834, hlam, p11843_1]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h11836, hlam, p11843_1]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h8887, hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h11479, hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h10681, h11481, h11833, h8887, hc23, hc34, hlam, hphi, p11843_1]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h11840, hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h8888, hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h11480, hlam, p11843_0]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h10681, h11481, h11833, h8888, hc23, hc34, hlam, hphi, p11843_1]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [h10681, h11481, h11833, h11834, h8888, hc23, hc34, hlam, hphi, p11843_1]
                    · have p11843_0 := h11843c.1
                      have p11843_1 := h11843c.2.1
                      have p11843_2 := h11843c.2.2.1
                      have p11843_3 := h11843c.2.2.2
                      linarith only [hlam, p11843_0]
                  · linarith only [h11481, h11833, h11842, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h11964 | h11964
            · linarith only [h11964, h8886, h8889, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11966 | h11966
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11967 | h11967
                · linarith only [h11833, h11967, h6874, h8887, hlam]
                · linarith only [h11964, h11966, h11967, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h11970 | h11970
                · linarith only [h11833, h11970, h6874, h8887, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h11972 | h11972
                  · linarith only [h11833, h11972, h6874, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases h2bigk with h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c | h11974c
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [h0, hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      rcases p11974_3 (m.d 0 2) (by simp) with h11977 | h11977
                      · rcases p11974_3 (m.d 1 2) (by simp) with h11978 | h11978
                        · rcases p11974_3 (m.d 2 3) (by simp) with h11979 | h11979
                          · linarith only [h11979, hlam, p11974_0]
                          · rcases p11974_3 (m.d 2 4) (by simp) with h11981 | h11981
                            · linarith only [h11981, h8887, hlam]
                            · linarith only [h11964, h11981, hlam]
                        · linarith only [h11478, h11978, hlam]
                      · linarith only [h11977, hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      rcases p11974_3 (m.d 0 2) (by simp) with h11986 | h11986
                      · rcases p11974_3 (m.d 1 2) (by simp) with h11987 | h11987
                        · rcases p11974_3 (m.d 2 3) (by simp) with h11988 | h11988
                          · linarith only [h11988, h8886, hlam]
                          · rcases p11974_3 (m.d 2 4) (by simp) with h11990 | h11990
                            · linarith only [h11990, hlam, p11974_0]
                            · rcases p11974_3 (m.d 2 5) (by simp) with h11992 | h11992
                              · linarith only [h11992, h8888, hlam]
                              · linarith only [h11970, h11992, hlam]
                        · linarith only [h11479, h11987, hlam]
                      · linarith only [h11986, hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      rcases p11974_3 (m.d 0 2) (by simp) with h11997 | h11997
                      · rcases p11974_3 (m.d 1 2) (by simp) with h11998 | h11998
                        · rcases p11974_3 (m.d 2 3) (by simp) with h11999 | h11999
                          · linarith only [h11999, h8886, hlam]
                          · rcases p11974_3 (m.d 2 4) (by simp) with h12001 | h12001
                            · linarith only [h12001, h8887, hlam]
                            · rcases p11974_3 (m.d 2 5) (by simp) with h12003 | h12003
                              · linarith only [h12003, hlam, p11974_0]
                              · rcases h4bigk with h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c | h12005c
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [hlam, p12005_0]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h6874, hlam, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11964, h11972, h8889, hc23, hc45, hlam, hphi, ht34, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h8889, hlam, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h10681, hlam, p12005_0]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11833, h6874, hc01, hc15, hlam, hphi, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [hlam, p12005_0]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11481, h11964, h11972, hc23, hc45, hlam, hphi, ht34, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11481, hlam, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11833, hlam, p12005_0]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h8887, hlam, p12005_0]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11479, hlam, p12005_0]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [hlam, p12005_0]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11964, hlam, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11970, hlam, p12005_0]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11972, h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11972, hc14, hc45, hlam, hphi, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11964, h11972, hc23, hc45, hlam, hphi, ht34, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [hlam, p12005_0]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11972, hlam, p12005_0]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [h11964, hc23, hc45, hlam, hphi, ht34, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p12005_1]
                                · have p12005_0 := h12005c.1
                                  have p12005_1 := h12005c.2.1
                                  have p12005_2 := h12005c.2.2.1
                                  have p12005_3 := h12005c.2.2.2
                                  linarith only [hlam, p12005_0]
                        · linarith only [h11480, h11998, hlam]
                      · linarith only [h11997, hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      rcases p11974_3 (m.d 0 2) (by simp) with h12033 | h12033
                      · linarith only [h0, h12033, hlam]
                      · rcases p11974_3 (m.d 1 2) (by simp) with h12035 | h12035
                        · rcases p11974_3 (m.d 2 3) (by simp) with h12036 | h12036
                          · linarith only [h11478, h12036, hlam]
                          · rcases p11974_3 (m.d 2 4) (by simp) with h12038 | h12038
                            · linarith only [h11479, h12038, hlam]
                            · rcases p11974_3 (m.d 2 5) (by simp) with h12040 | h12040
                              · linarith only [h11480, h12040, hlam]
                              · rcases h4bigk with h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c | h12042c
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [hlam, p12042_0]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h6874, hlam, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11481, h11964, h6874, hc23, hc34, hlam, hphi, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h8889, hlam, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h10681, hlam, p12042_0]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11481, h11972, h6874, hc01, hc35, hlam, hphi, ht12, ht23, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [hlam, p12042_0]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11481, h11964, h11972, hc23, hc35, hlam, hphi, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11481, hlam, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11833, hlam, p12042_0]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h8887, hlam, p12042_0]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11479, hlam, p12042_0]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [hlam, p12042_0]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11964, hlam, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11970, hlam, p12042_0]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11964, h11970, h11972, h6874, h8888, hc01, hc12, hc23, hc35, hlam, hphi, p11974_1, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11964, h11970, h11972, h6874, h8888, hc01, hc12, hc23, hc35, hlam, hphi, p11974_1, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11964, h11972, hc23, hc35, hlam, hphi, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [hlam, p12042_0]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11972, hlam, p12042_0]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11964, h11970, h6874, h8888, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p11974_1, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11964, h11970, h6874, h8888, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p11974_1, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [h11964, hc23, hc45, hlam, hphi, ht34, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p12042_1]
                                · have p12042_0 := h12042c.1
                                  have p12042_1 := h12042c.2.1
                                  have p12042_2 := h12042c.2.2.1
                                  have p12042_3 := h12042c.2.2.2
                                  linarith only [hlam, p12042_0]
                        · linarith only [h0, h12035, hlam]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      rcases p11974_3 (m.d 0 2) (by simp) with h12070 | h12070
                      · linarith only [h0, h12070, hlam]
                      · linarith only [h12070, h8886, hlam]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      rcases p11974_3 (m.d 0 2) (by simp) with h12073 | h12073
                      · linarith only [h0, h12073, hlam]
                      · linarith only [h12073, h8887, hlam]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      rcases p11974_3 (m.d 0 2) (by simp) with h12076 | h12076
                      · linarith only [h0, h12076, hlam]
                      · linarith only [h12076, h8888, hlam]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [h8886, hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [h11478, hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [h11964, hlam, p11974_1]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [h11966, hlam, p11974_1]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [h8887, hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [h11479, hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [h10681, h8887, hc23, hc45, hlam, hphi, ht34, p11974_1]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [h11970, hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [h8888, hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [h11480, hlam, p11974_0]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      rcases p11974_3 (m.d 0 2) (by simp) with h12091 | h12091
                      · rcases p11974_3 (m.d 1 2) (by simp) with h12092 | h12092
                        · rcases p11974_3 (m.d 2 3) (by simp) with h12093 | h12093
                          · linarith only [h11966, h12093, hlam]
                          · rcases p11974_3 (m.d 2 4) (by simp) with h12095 | h12095
                            · linarith only [h11970, h12095, hlam]
                            · linarith only [h11964, h12095, hlam]
                        · linarith only [h11478, h12092, hlam]
                      · linarith only [h12091, h8886, hlam]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      rcases p11974_3 (m.d 0 2) (by simp) with h12100 | h12100
                      · rcases p11974_3 (m.d 1 2) (by simp) with h12101 | h12101
                        · rcases p11974_3 (m.d 2 3) (by simp) with h12102 | h12102
                          · linarith only [h11966, h12102, hlam]
                          · rcases p11974_3 (m.d 2 4) (by simp) with h12104 | h12104
                            · linarith only [h11970, h12104, hlam]
                            · rcases p11974_3 (m.d 2 5) (by simp) with h12106 | h12106
                              · rcases h4bigk with h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c | h12107c
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [hlam, p12107_0]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h6874, hlam, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11481, h11964, h11972, h6874, hc23, hc45, hlam, hphi, ht34, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h8889, hlam, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h10681, hlam, p12107_0]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11481, h11972, hc04, hc45, hlam, hphi, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [hlam, p12107_0]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11481, h11964, h11972, hc23, hc45, hlam, hphi, ht34, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11481, hlam, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11833, hlam, p12107_0]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h8887, hlam, p12107_0]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11479, hlam, p12107_0]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [hlam, p12107_0]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11964, hlam, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11970, hlam, p12107_0]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h0, h11964, h11972, h6874, h8888, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p11974_1, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11972, hc14, hc45, hlam, hphi, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11964, h11972, hc23, hc45, hlam, hphi, ht34, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [hlam, p12107_0]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11972, hlam, p12107_0]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h0, h11964, h6874, h8888, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p11974_1, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h0, h11964, h6874, h8888, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p11974_1, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [h11964, hc23, hc45, hlam, hphi, ht34, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [hc34, hc45, hlam, hphi, p12107_1]
                                · have p12107_0 := h12107c.1
                                  have p12107_1 := h12107c.2.1
                                  have p12107_2 := h12107c.2.2.1
                                  have p12107_3 := h12107c.2.2.2
                                  linarith only [hlam, p12107_0]
                              · linarith only [h11970, h12106, hlam]
                        · linarith only [h11479, h12101, hlam]
                      · linarith only [h12100, h8887, hlam]
                    · have p11974_0 := h11974c.1
                      have p11974_1 := h11974c.2.1
                      have p11974_2 := h11974c.2.2.1
                      have p11974_3 := h11974c.2.2.2
                      linarith only [hlam, p11974_0]
      · linarith only [h0, h11480, h8888, hlam]
    · linarith only [h0, h11479, h8887, hlam]
  · linarith only [h0, h11478, h8886, h8889, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 0 4 5 (by decide) (by decide) with h10681 | h10681
  · exact r1l7_12_24_L_I_H_I_s10_x1_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h10681
  · exact r1l7_12_24_L_I_H_I_s10_x1_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h10681

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 0 3 4 (by decide) (by decide) with h8889 | h8889
  · exact r1l7_12_24_L_I_H_I_s10_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889
  · exact r1l7_12_24_L_I_H_I_s10_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889

end R2N4
