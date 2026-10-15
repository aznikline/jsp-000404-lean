import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 0 4 5 (by decide) (by decide) with h11474 | h11474
  · linarith only [h11474, h9250, h9251, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h11476 | h11476
    · linarith only [h0, h11476, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h11478 | h11478
      · linarith only [h0, h11478, h7337, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h11480 | h11480
        · linarith only [h0, h11480, h8360, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h11482 | h11482
          · rcases m.htr 1 3 5 (by decide) (by decide) with h11483 | h11483
            · linarith only [h1, h11483, h9251, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h11485 | h11485
              · linarith only [h11474, h11485, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h11487 | h11487
                · rcases m.htr 2 3 5 (by decide) (by decide) with h11488 | h11488
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11489 | h11489
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h11490 | h11490
                      · linarith only [h1, h11474, h11482, h11488, h11490, h2, h9251, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases h0bigk with h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c | h11492c
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [hlam, p11492_0]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          rcases p11492_3 (m.d 0 1) (by simp) with h11494 | h11494
                          · rcases p11492_3 (m.d 0 2) (by simp) with h11495 | h11495
                            · linarith only [h0, h11495, hlam]
                            · rcases p11492_3 (m.d 0 3) (by simp) with h11497 | h11497
                              · linarith only [h1, h11497, hlam]
                              · linarith only [h11497, h4, hlam]
                          · linarith only [h0, h11494, hlam]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          rcases p11492_3 (m.d 0 1) (by simp) with h11501 | h11501
                          · rcases p11492_3 (m.d 0 2) (by simp) with h11502 | h11502
                            · linarith only [h0, h11502, hlam]
                            · rcases p11492_3 (m.d 0 3) (by simp) with h11504 | h11504
                              · linarith only [h1, h11504, hlam]
                              · rcases p11492_3 (m.d 0 4) (by simp) with h11506 | h11506
                                · linarith only [h11506, h2, hlam]
                                · rcases p11492_3 (m.d 0 5) (by simp) with h11508 | h11508
                                  · linarith only [h11508, h3, hlam]
                                  · linarith only [h11508, h9251, hlam]
                          · linarith only [h1, h11501, hlam]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          rcases p11492_3 (m.d 0 1) (by simp) with h11512 | h11512
                          · rcases p11492_3 (m.d 0 2) (by simp) with h11513 | h11513
                            · linarith only [h0, h11513, hlam]
                            · rcases p11492_3 (m.d 0 3) (by simp) with h11515 | h11515
                              · linarith only [h1, h11515, hlam]
                              · linarith only [h11515, h9250, hlam]
                          · linarith only [h11512, h2, hlam]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          rcases p11492_3 (m.d 0 1) (by simp) with h11519 | h11519
                          · rcases p11492_3 (m.d 0 2) (by simp) with h11520 | h11520
                            · linarith only [h0, h11520, hlam]
                            · rcases p11492_3 (m.d 0 3) (by simp) with h11522 | h11522
                              · linarith only [h1, h11522, hlam]
                              · rcases p11492_3 (m.d 0 4) (by simp) with h11524 | h11524
                                · linarith only [h11524, h2, hlam]
                                · rcases p11492_3 (m.d 0 5) (by simp) with h11526 | h11526
                                  · linarith only [h11526, h3, hlam]
                                  · rcases h2bigk with h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c | h11528c
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p11528_1]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h4, hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h7337, hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h8360, hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h0, hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h11476, hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h11478, hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h11480, hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      rcases p11528_3 (m.d 0 2) (by simp) with h11539 | h11539
                                      · linarith only [h11539, hlam, p11528_0]
                                      · rcases p11528_3 (m.d 1 2) (by simp) with h11541 | h11541
                                        · linarith only [h11476, h11541, hlam]
                                        · rcases p11528_3 (m.d 2 3) (by simp) with h11543 | h11543
                                          · rcases p11528_3 (m.d 2 4) (by simp) with h11544 | h11544
                                            · linarith only [h11487, h11544, hlam]
                                            · linarith only [h11544, h7337, hlam]
                                          · linarith only [h11543, hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      rcases p11528_3 (m.d 0 2) (by simp) with h11548 | h11548
                                      · linarith only [h11548, h4, hlam]
                                      · linarith only [h0, h11548, hlam]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h11489, h11490, h7337, h9250, h9251, hc02, hc23, hlam, hphi, p11528_1]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h0, h8360, hc12, hc23, hlam, hphi, p11528_1]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      rcases p11528_3 (m.d 0 2) (by simp) with h11554 | h11554
                                      · linarith only [h11554, hlam, p11528_0]
                                      · rcases p11528_3 (m.d 1 2) (by simp) with h11556 | h11556
                                        · linarith only [h11478, h11556, hlam]
                                        · rcases p11528_3 (m.d 2 3) (by simp) with h11558 | h11558
                                          · rcases p11528_3 (m.d 2 4) (by simp) with h11559 | h11559
                                            · rcases p11528_3 (m.d 2 5) (by simp) with h11560 | h11560
                                              · linarith only [h11489, h11560, hlam]
                                              · linarith only [h11560, h8360, hlam]
                                            · linarith only [h11559, hlam, p11528_0]
                                          · linarith only [h11558, h4, hlam]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      rcases p11528_3 (m.d 0 2) (by simp) with h11565 | h11565
                                      · linarith only [h11565, h7337, hlam]
                                      · linarith only [h0, h11565, hlam]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h11487, hlam, p11528_1]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h1, h11482, h11489, h11490, h9251, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11528_1]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      rcases p11528_3 (m.d 0 2) (by simp) with h11571 | h11571
                                      · linarith only [h11571, hlam, p11528_0]
                                      · rcases p11528_3 (m.d 1 2) (by simp) with h11573 | h11573
                                        · linarith only [h11480, h11573, hlam]
                                        · rcases p11528_3 (m.d 2 3) (by simp) with h11575 | h11575
                                          · rcases p11528_3 (m.d 2 4) (by simp) with h11576 | h11576
                                            · rcases p11528_3 (m.d 2 5) (by simp) with h11577 | h11577
                                              · rcases h3bigk with h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c | h11578c
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [hlam, p11578_0]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h11482, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h4, hlam, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h11490, h9251, hc34, hc45, hlam, hphi, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h9251, hlam, p11578_0]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h1, hlam, p11578_0]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [hlam, p11578_0]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h11476, hlam, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h11483, hlam, p11578_0]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h11476, hc12, hc23, hlam, hphi, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [hlam, p11578_0]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  rcases p11578_3 (m.d 0 3) (by simp) with h11592 | h11592
                                                  · linarith only [h11592, h4, hlam]
                                                  · linarith only [h11592, h9250, hlam]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h1, h11482, h9251, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h9250, hlam, p11578_0]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h11482, hlam, p11578_0]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h11487, hlam, p11578_0]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [hlam, p11578_0]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h11490, hlam, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h1, h11482, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h11482, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h11488, hlam, p11578_0]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [h11487, h11489, h11490, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11578_1]
                                                · have p11578_0 := h11578c.1
                                                  have p11578_1 := h11578c.2.1
                                                  have p11578_2 := h11578c.2.2.1
                                                  have p11578_3 := h11578c.2.2.2
                                                  linarith only [hlam, p11578_0]
                                              · linarith only [h11577, hlam, p11528_0]
                                            · linarith only [h11576, h7337, hlam]
                                          · linarith only [h11575, h4, hlam]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      rcases p11528_3 (m.d 0 2) (by simp) with h11609 | h11609
                                      · linarith only [h11609, h8360, hlam]
                                      · linarith only [h0, h11609, hlam]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h11488, hlam, p11528_1]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [h11489, hlam, p11528_0]
                                    · have p11528_0 := h11528c.1
                                      have p11528_1 := h11528c.2.1
                                      have p11528_2 := h11528c.2.2.1
                                      have p11528_3 := h11528c.2.2.2
                                      linarith only [hlam, p11528_0]
                          · linarith only [h11519, h3, hlam]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h0, hlam, p11492_0]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [hlam, p11492_0]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h4, hlam, p11492_0]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h7337, hlam, p11492_1]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h8360, hlam, p11492_0]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h1, hlam, p11492_1]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h0, h11487, h11489, h11490, h9251, hc12, hc23, hlam, hphi, p11492_1]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [hlam, p11492_0]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h0, h11487, h11489, h11490, h7337, h9251, hc12, hc23, hlam, hphi, p11492_1]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h9251, hlam, p11492_1]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h2, hlam, p11492_0]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h0, h11487, h11489, h11490, h9250, h9251, hc12, hc23, hlam, hphi, p11492_1]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h9250, hlam, p11492_0]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [hlam, p11492_0]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h11474, hlam, p11492_0]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h3, hlam, p11492_0]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h0, h11487, h11489, h11490, h9251, hc12, hc23, hlam, hphi, p11492_1]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h1, h11482, h11487, h11489, h11490, h9251, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11492_1]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [h11478, h11487, h11489, h11490, h2, h9251, hc12, hc23, hlam, hphi, p11492_1]
                        · have p11492_0 := h11492c.1
                          have p11492_1 := h11492c.2.1
                          have p11492_2 := h11492c.2.2.1
                          have p11492_3 := h11492c.2.2.2
                          linarith only [hlam, p11492_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h11636 | h11636
                      · linarith only [h1, h11482, h11489, h11636, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c | h11638c
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [hlam, p11638_0]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          rcases p11638_3 (m.d 0 1) (by simp) with h11640 | h11640
                          · rcases p11638_3 (m.d 0 2) (by simp) with h11641 | h11641
                            · linarith only [h0, h11641, hlam]
                            · rcases p11638_3 (m.d 0 3) (by simp) with h11643 | h11643
                              · linarith only [h1, h11643, hlam]
                              · linarith only [h11643, h4, hlam]
                          · linarith only [h0, h11640, hlam]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          rcases p11638_3 (m.d 0 1) (by simp) with h11647 | h11647
                          · rcases p11638_3 (m.d 0 2) (by simp) with h11648 | h11648
                            · linarith only [h0, h11648, hlam]
                            · rcases p11638_3 (m.d 0 3) (by simp) with h11650 | h11650
                              · linarith only [h1, h11650, hlam]
                              · rcases p11638_3 (m.d 0 4) (by simp) with h11652 | h11652
                                · linarith only [h11652, h2, hlam]
                                · rcases p11638_3 (m.d 0 5) (by simp) with h11654 | h11654
                                  · linarith only [h11654, h3, hlam]
                                  · linarith only [h11654, h9251, hlam]
                          · linarith only [h1, h11647, hlam]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          rcases p11638_3 (m.d 0 1) (by simp) with h11658 | h11658
                          · rcases p11638_3 (m.d 0 2) (by simp) with h11659 | h11659
                            · linarith only [h0, h11659, hlam]
                            · rcases p11638_3 (m.d 0 3) (by simp) with h11661 | h11661
                              · linarith only [h1, h11661, hlam]
                              · linarith only [h11661, h9250, hlam]
                          · linarith only [h11658, h2, hlam]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          rcases p11638_3 (m.d 0 1) (by simp) with h11665 | h11665
                          · rcases p11638_3 (m.d 0 2) (by simp) with h11666 | h11666
                            · linarith only [h0, h11666, hlam]
                            · rcases p11638_3 (m.d 0 3) (by simp) with h11668 | h11668
                              · linarith only [h1, h11668, hlam]
                              · rcases p11638_3 (m.d 0 4) (by simp) with h11670 | h11670
                                · linarith only [h11670, h2, hlam]
                                · rcases p11638_3 (m.d 0 5) (by simp) with h11672 | h11672
                                  · linarith only [h11672, h3, hlam]
                                  · rcases h2bigk with h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c | h11674c
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h7337, hc12, hc24, hlam, hphi, p11674_1]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h4, hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h7337, hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h8360, hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h0, hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h11476, hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h11478, hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h11480, hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      rcases p11674_3 (m.d 0 2) (by simp) with h11685 | h11685
                                      · linarith only [h11685, hlam, p11674_0]
                                      · rcases p11674_3 (m.d 1 2) (by simp) with h11687 | h11687
                                        · linarith only [h11476, h11687, hlam]
                                        · rcases p11674_3 (m.d 2 3) (by simp) with h11689 | h11689
                                          · rcases p11674_3 (m.d 2 4) (by simp) with h11690 | h11690
                                            · linarith only [h11487, h11690, hlam]
                                            · linarith only [h11690, h7337, hlam]
                                          · linarith only [h11689, hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      rcases p11674_3 (m.d 0 2) (by simp) with h11694 | h11694
                                      · linarith only [h11694, h4, hlam]
                                      · linarith only [h0, h11694, hlam]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h7337, hc02, hc23, hlam, hphi, p11674_1]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h0, h8360, hc12, hc23, hlam, hphi, p11674_1]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h0, h11489, hc12, hc45, hlam, hphi, ht23, ht34, p11674_1]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h11489, hc12, hc45, hlam, hphi, ht23, ht34, p11674_1]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h11487, hlam, p11674_1]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [hlam, p11674_0]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h11489, hlam, p11674_1]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      rcases p11674_3 (m.d 0 2) (by simp) with h11705 | h11705
                                      · linarith only [h11705, hlam, p11674_0]
                                      · rcases p11674_3 (m.d 1 2) (by simp) with h11707 | h11707
                                        · linarith only [h11480, h11707, hlam]
                                        · rcases p11674_3 (m.d 2 3) (by simp) with h11709 | h11709
                                          · rcases p11674_3 (m.d 2 4) (by simp) with h11710 | h11710
                                            · linarith only [h11489, h11710, hlam]
                                            · linarith only [h11710, h7337, hlam]
                                          · linarith only [h11709, h4, hlam]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      rcases p11674_3 (m.d 0 2) (by simp) with h11714 | h11714
                                      · linarith only [h11714, h8360, hlam]
                                      · linarith only [h0, h11714, hlam]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h11488, hlam, p11674_1]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [h0, h7337, hc12, hc25, hlam, hphi, p11674_1]
                                    · have p11674_0 := h11674c.1
                                      have p11674_1 := h11674c.2.1
                                      have p11674_2 := h11674c.2.2.1
                                      have p11674_3 := h11674c.2.2.2
                                      linarith only [hlam, p11674_0]
                          · linarith only [h11665, h3, hlam]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h0, hlam, p11638_0]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [hlam, p11638_0]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h4, hlam, p11638_0]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h7337, hlam, p11638_1]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h8360, hlam, p11638_0]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h1, hlam, p11638_1]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h0, h11488, h9251, hc12, hc23, hlam, hphi, p11638_1]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [hlam, p11638_0]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h0, h11488, h7337, h9251, hc12, hc23, hlam, hphi, p11638_1]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h9251, hlam, p11638_1]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h2, hlam, p11638_0]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h0, h11488, h9250, h9251, hc12, hc23, hlam, hphi, p11638_1]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h9250, hlam, p11638_0]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [hlam, p11638_0]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h11474, hlam, p11638_0]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h3, hlam, p11638_0]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h0, h11488, h9251, hc12, hc23, hlam, hphi, p11638_1]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h1, h11482, h11488, h9251, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11638_1]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [h11478, h11488, h2, h9251, hc12, hc23, hlam, hphi, p11638_1]
                        · have p11638_0 := h11638c.1
                          have p11638_1 := h11638c.2.1
                          have p11638_2 := h11638c.2.2.1
                          have p11638_3 := h11638c.2.2.2
                          linarith only [hlam, p11638_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11741 | h11741
                    · linarith only [h11474, h11478, h11487, h11488, h11741, h2, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h11743 | h11743
                      · linarith only [h0, h1, h11482, h11741, h11743, h7337, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h0bigk with h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c | h11745c
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [hlam, p11745_0]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          rcases p11745_3 (m.d 0 1) (by simp) with h11747 | h11747
                          · rcases p11745_3 (m.d 0 2) (by simp) with h11748 | h11748
                            · linarith only [h0, h11748, hlam]
                            · rcases p11745_3 (m.d 0 3) (by simp) with h11750 | h11750
                              · linarith only [h1, h11750, hlam]
                              · linarith only [h11750, h4, hlam]
                          · linarith only [h0, h11747, hlam]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          rcases p11745_3 (m.d 0 1) (by simp) with h11754 | h11754
                          · rcases p11745_3 (m.d 0 2) (by simp) with h11755 | h11755
                            · linarith only [h0, h11755, hlam]
                            · rcases p11745_3 (m.d 0 3) (by simp) with h11757 | h11757
                              · linarith only [h1, h11757, hlam]
                              · rcases p11745_3 (m.d 0 4) (by simp) with h11759 | h11759
                                · linarith only [h11759, h2, hlam]
                                · rcases p11745_3 (m.d 0 5) (by simp) with h11761 | h11761
                                  · linarith only [h11761, h3, hlam]
                                  · linarith only [h11761, h9251, hlam]
                          · linarith only [h1, h11754, hlam]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          rcases p11745_3 (m.d 0 1) (by simp) with h11765 | h11765
                          · rcases p11745_3 (m.d 0 2) (by simp) with h11766 | h11766
                            · linarith only [h0, h11766, hlam]
                            · rcases p11745_3 (m.d 0 3) (by simp) with h11768 | h11768
                              · linarith only [h1, h11768, hlam]
                              · linarith only [h11768, h9250, hlam]
                          · linarith only [h11765, h2, hlam]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          rcases p11745_3 (m.d 0 1) (by simp) with h11772 | h11772
                          · rcases p11745_3 (m.d 0 2) (by simp) with h11773 | h11773
                            · linarith only [h0, h11773, hlam]
                            · rcases p11745_3 (m.d 0 3) (by simp) with h11775 | h11775
                              · linarith only [h1, h11775, hlam]
                              · rcases p11745_3 (m.d 0 4) (by simp) with h11777 | h11777
                                · linarith only [h11777, h2, hlam]
                                · rcases p11745_3 (m.d 0 5) (by simp) with h11779 | h11779
                                  · linarith only [h11779, h3, hlam]
                                  · rcases h2bigk with h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c | h11781c
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h7337, hc12, hc24, hlam, hphi, p11781_1]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h4, hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h7337, hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h8360, hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h0, hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h11476, hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h11478, hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h11480, hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h11488, h11743, hc02, hc45, hlam, hphi, ht23, ht34, p11781_1]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h11488, h11743, hc12, hc45, hlam, hphi, ht23, ht34, p11781_1]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h11488, h11743, hc24, hc45, hlam, hphi, p11781_1]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h11488, hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h0, h11487, h11488, h11743, hc12, hc45, hlam, hphi, ht23, ht34, p11781_1]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h11487, h11488, h11743, hc12, hc45, hlam, hphi, ht23, ht34, p11781_1]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h11487, hlam, p11781_1]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [hlam, p11781_0]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h11741, hlam, p11781_1]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      rcases p11781_3 (m.d 0 2) (by simp) with h11802 | h11802
                                      · linarith only [h11802, hlam, p11781_0]
                                      · rcases p11781_3 (m.d 1 2) (by simp) with h11804 | h11804
                                        · linarith only [h11480, h11804, hlam]
                                        · rcases p11781_3 (m.d 2 3) (by simp) with h11806 | h11806
                                          · linarith only [h11488, h11806, hlam]
                                          · linarith only [h11806, h4, hlam]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      rcases p11781_3 (m.d 0 2) (by simp) with h11809 | h11809
                                      · linarith only [h11809, h8360, hlam]
                                      · linarith only [h0, h11809, hlam]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h0, h11488, h11743, h4, hc12, hc45, hlam, hphi, ht23, ht34, p11781_1]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [h0, h11488, h11743, h7337, hc12, hc45, hlam, hphi, ht23, ht34, p11781_1]
                                    · have p11781_0 := h11781c.1
                                      have p11781_1 := h11781c.2.1
                                      have p11781_2 := h11781c.2.2.1
                                      have p11781_3 := h11781c.2.2.2
                                      linarith only [hlam, p11781_0]
                          · linarith only [h11772, h3, hlam]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h0, hlam, p11745_0]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [hlam, p11745_0]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h4, hlam, p11745_0]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h7337, hlam, p11745_1]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h8360, hlam, p11745_0]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h1, hlam, p11745_1]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h0, h11743, h9251, hc12, hc45, hlam, hphi, ht23, ht34, p11745_1]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [hlam, p11745_0]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h0, h11743, h7337, h9251, hc12, hc45, hlam, hphi, ht23, ht34, p11745_1]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h9251, hlam, p11745_1]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h2, hlam, p11745_0]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h0, h11743, h9250, h9251, hc12, hc45, hlam, hphi, ht23, ht34, p11745_1]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h9250, hlam, p11745_0]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [hlam, p11745_0]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h11474, hlam, p11745_0]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h3, hlam, p11745_0]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          rcases p11745_3 (m.d 0 1) (by simp) with h11832 | h11832
                          · rcases p11745_3 (m.d 0 2) (by simp) with h11833 | h11833
                            · linarith only [h11833, h8360, hlam]
                            · rcases p11745_3 (m.d 0 3) (by simp) with h11835 | h11835
                              · linarith only [h11835, h9251, hlam]
                              · linarith only [h11835, h4, hlam]
                          · linarith only [h0, h11832, hlam]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [h1, h11482, h11488, h11743, h8360, hc34, hc45, hlam, hphi, p11745_1]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          rcases p11745_3 (m.d 0 1) (by simp) with h11840 | h11840
                          · rcases p11745_3 (m.d 0 2) (by simp) with h11841 | h11841
                            · linarith only [h11841, h8360, hlam]
                            · rcases p11745_3 (m.d 0 3) (by simp) with h11843 | h11843
                              · linarith only [h11843, h9251, hlam]
                              · linarith only [h11843, h9250, hlam]
                          · linarith only [h11840, h2, hlam]
                        · have p11745_0 := h11745c.1
                          have p11745_1 := h11745c.2.1
                          have p11745_2 := h11745c.2.2.1
                          have p11745_3 := h11745c.2.2.2
                          linarith only [hlam, p11745_0]
                · linarith only [h0, h1, h11482, h11487, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h11482, h9250, h9251, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 0 3 5 (by decide) (by decide) with h9251 | h9251
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251
  · exact r1l7_10_12_23_L_I_L_I_H_I_s13_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 hg9250 h9251

set_option maxHeartbeats 7336000 in
set_option maxHeartbeats 7336000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s12_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  exact r1l7_10_12_23_L_I_L_I_H_I_s13 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h7337 h8360 h9250

set_option maxHeartbeats 7336000 in
set_option maxHeartbeats 7336000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s12_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h9250 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h11850 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  rcases m.htr 0 4 5 (by decide) (by decide) with h11851 | h11851
  · rcases m.htr 1 2 3 (by decide) (by decide) with h11852 | h11852
    · linarith only [h0, h11852, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h11854 | h11854
      · linarith only [h0, h11854, h7337, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h11856 | h11856
        · linarith only [h0, h11856, h8360, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h11858 | h11858
          · linarith only [h1, h11850, h11858, h9250, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h11860 | h11860
            · rcases m.htr 1 4 5 (by decide) (by decide) with h11861 | h11861
              · rcases m.htr 2 3 4 (by decide) (by decide) with h11862 | h11862
                · rcases m.htr 2 3 5 (by decide) (by decide) with h11863 | h11863
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11864 | h11864
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h11865 | h11865
                      · rcases h0bigk with h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c | h11866c
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [hlam, p11866_0]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          rcases p11866_3 (m.d 0 1) (by simp) with h11868 | h11868
                          · rcases p11866_3 (m.d 0 2) (by simp) with h11869 | h11869
                            · linarith only [h0, h11869, hlam]
                            · rcases p11866_3 (m.d 0 3) (by simp) with h11871 | h11871
                              · linarith only [h1, h11871, hlam]
                              · linarith only [h11871, h4, hlam]
                          · linarith only [h0, h11868, hlam]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          rcases p11866_3 (m.d 0 1) (by simp) with h11875 | h11875
                          · rcases p11866_3 (m.d 0 2) (by simp) with h11876 | h11876
                            · linarith only [h0, h11876, hlam]
                            · rcases p11866_3 (m.d 0 3) (by simp) with h11878 | h11878
                              · linarith only [h1, h11878, hlam]
                              · rcases p11866_3 (m.d 0 4) (by simp) with h11880 | h11880
                                · linarith only [h11880, h2, hlam]
                                · linarith only [h11880, h9250, hlam]
                          · linarith only [h1, h11875, hlam]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          rcases p11866_3 (m.d 0 1) (by simp) with h11884 | h11884
                          · rcases p11866_3 (m.d 0 2) (by simp) with h11885 | h11885
                            · linarith only [h0, h11885, hlam]
                            · rcases p11866_3 (m.d 0 3) (by simp) with h11887 | h11887
                              · linarith only [h1, h11887, hlam]
                              · rcases p11866_3 (m.d 0 4) (by simp) with h11889 | h11889
                                · linarith only [h11889, h2, hlam]
                                · rcases p11866_3 (m.d 0 5) (by simp) with h11891 | h11891
                                  · linarith only [h11891, h3, hlam]
                                  · rcases h2bigk with h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c | h11893c
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h8360, hc12, hc25, hlam, hphi, p11893_1]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h4, hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h7337, hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h8360, hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h0, hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h11852, hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h11854, hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h11856, hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      rcases p11893_3 (m.d 0 2) (by simp) with h11904 | h11904
                                      · linarith only [h11904, hlam, p11893_0]
                                      · rcases p11893_3 (m.d 1 2) (by simp) with h11906 | h11906
                                        · linarith only [h11852, h11906, hlam]
                                        · rcases p11893_3 (m.d 2 3) (by simp) with h11908 | h11908
                                          · rcases p11893_3 (m.d 2 4) (by simp) with h11909 | h11909
                                            · linarith only [h11862, h11909, hlam]
                                            · linarith only [h11909, h7337, hlam]
                                          · linarith only [h11908, hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      rcases p11893_3 (m.d 0 2) (by simp) with h11913 | h11913
                                      · linarith only [h11913, h4, hlam]
                                      · linarith only [h0, h11913, hlam]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h7337, hc02, hc23, hlam, hphi, p11893_1]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h0, h8360, hc12, hc23, hlam, hphi, p11893_1]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      rcases p11893_3 (m.d 0 2) (by simp) with h11919 | h11919
                                      · linarith only [h11919, hlam, p11893_0]
                                      · rcases p11893_3 (m.d 1 2) (by simp) with h11921 | h11921
                                        · linarith only [h11854, h11921, hlam]
                                        · rcases p11893_3 (m.d 2 3) (by simp) with h11923 | h11923
                                          · rcases p11893_3 (m.d 2 4) (by simp) with h11924 | h11924
                                            · rcases p11893_3 (m.d 2 5) (by simp) with h11925 | h11925
                                              · linarith only [h11864, h11925, hlam]
                                              · linarith only [h11925, h8360, hlam]
                                            · linarith only [h11924, hlam, p11893_0]
                                          · linarith only [h11923, h4, hlam]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      rcases p11893_3 (m.d 0 2) (by simp) with h11930 | h11930
                                      · linarith only [h11930, h7337, hlam]
                                      · linarith only [h0, h11930, hlam]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h11862, hlam, p11893_1]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h0, h8360, hc12, hc24, hlam, hphi, p11893_1]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      rcases p11893_3 (m.d 0 2) (by simp) with h11936 | h11936
                                      · linarith only [h11936, hlam, p11893_0]
                                      · rcases p11893_3 (m.d 1 2) (by simp) with h11938 | h11938
                                        · linarith only [h11856, h11938, hlam]
                                        · rcases p11893_3 (m.d 2 3) (by simp) with h11940 | h11940
                                          · rcases p11893_3 (m.d 2 4) (by simp) with h11941 | h11941
                                            · rcases p11893_3 (m.d 2 5) (by simp) with h11942 | h11942
                                              · rcases h3bigk with h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c | h11943c
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11862, h9250, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11943_1]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h4, hlam, p11943_1]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h9250, hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11862, h11865, h9250, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11943_1]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h1, hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11852, hlam, p11943_1]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11858, hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h1, h11865, hc01, hc45, hlam, hphi, ht0b, ht5b, p11943_1]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h0, h4, hc12, hc23, hlam, hphi, p11943_1]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11852, hc12, hc23, hlam, hphi, p11943_1]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11850, h11865, h9250, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11943_1]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  rcases p11943_3 (m.d 0 3) (by simp) with h11958 | h11958
                                                  · linarith only [h11958, h4, hlam]
                                                  · linarith only [h11850, h11958, hlam]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h1, h11860, h11865, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11943_1]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11860, h11865, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11943_1]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11862, hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11862, h11865, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11943_1]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11850, hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11860, hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11863, hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [h11865, hlam, p11943_0]
                                                · have p11943_0 := h11943c.1
                                                  have p11943_1 := h11943c.2.1
                                                  have p11943_2 := h11943c.2.2.1
                                                  have p11943_3 := h11943c.2.2.2
                                                  linarith only [hlam, p11943_0]
                                              · linarith only [h11942, hlam, p11893_0]
                                            · linarith only [h11941, h7337, hlam]
                                          · linarith only [h11940, h4, hlam]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      rcases p11893_3 (m.d 0 2) (by simp) with h11974 | h11974
                                      · linarith only [h11974, h8360, hlam]
                                      · linarith only [h0, h11974, hlam]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h11863, hlam, p11893_1]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [h11864, hlam, p11893_0]
                                    · have p11893_0 := h11893c.1
                                      have p11893_1 := h11893c.2.1
                                      have p11893_2 := h11893c.2.2.1
                                      have p11893_3 := h11893c.2.2.2
                                      linarith only [hlam, p11893_0]
                          · linarith only [h11884, h2, hlam]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          rcases p11866_3 (m.d 0 1) (by simp) with h11981 | h11981
                          · rcases p11866_3 (m.d 0 2) (by simp) with h11982 | h11982
                            · linarith only [h0, h11982, hlam]
                            · rcases p11866_3 (m.d 0 3) (by simp) with h11984 | h11984
                              · linarith only [h1, h11984, hlam]
                              · linarith only [h11850, h11984, hlam]
                          · linarith only [h11981, h3, hlam]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h0, hlam, p11866_0]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [hlam, p11866_0]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h4, hlam, p11866_0]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h7337, hlam, p11866_1]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h8360, hlam, p11866_0]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h1, hlam, p11866_1]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h0, h11862, h9250, hc12, hc23, hlam, hphi, p11866_1]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [hlam, p11866_0]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h9250, hlam, p11866_1]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h0, h11862, h8360, h9250, hc12, hc23, hlam, hphi, p11866_1]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h2, hlam, p11866_0]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h0, h11862, h9250, hc12, hc23, hlam, hphi, p11866_1]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h1, h11860, h11862, h11865, h9250, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11866_1]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [hlam, p11866_0]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h0, h11862, h8360, h9250, hc12, hc23, hlam, hphi, p11866_1]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h3, hlam, p11866_0]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h0, h11850, h11862, h9250, hc12, hc23, hlam, hphi, p11866_1]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h11850, hlam, p11866_0]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [h11851, hlam, p11866_1]
                        · have p11866_0 := h11866c.1
                          have p11866_1 := h11866c.2.1
                          have p11866_2 := h11866c.2.2.1
                          have p11866_3 := h11866c.2.2.2
                          linarith only [hlam, p11866_0]
                      · linarith only [h11851, h11865, h9250, hlam]
                    · linarith only [h0, h1, h11860, h11861, h11864, h7337, h9250, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h11862, h11863, h9250, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12011 | h12011
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12012 | h12012
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12013 | h12013
                      · rcases h0bigk with h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c | h12014c
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [hlam, p12014_0]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          rcases p12014_3 (m.d 0 1) (by simp) with h12016 | h12016
                          · rcases p12014_3 (m.d 0 2) (by simp) with h12017 | h12017
                            · linarith only [h0, h12017, hlam]
                            · rcases p12014_3 (m.d 0 3) (by simp) with h12019 | h12019
                              · linarith only [h1, h12019, hlam]
                              · linarith only [h12019, h4, hlam]
                          · linarith only [h0, h12016, hlam]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          rcases p12014_3 (m.d 0 1) (by simp) with h12023 | h12023
                          · rcases p12014_3 (m.d 0 2) (by simp) with h12024 | h12024
                            · linarith only [h0, h12024, hlam]
                            · rcases p12014_3 (m.d 0 3) (by simp) with h12026 | h12026
                              · linarith only [h1, h12026, hlam]
                              · rcases p12014_3 (m.d 0 4) (by simp) with h12028 | h12028
                                · linarith only [h12028, h2, hlam]
                                · linarith only [h12028, h9250, hlam]
                          · linarith only [h1, h12023, hlam]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          rcases p12014_3 (m.d 0 1) (by simp) with h12032 | h12032
                          · rcases p12014_3 (m.d 0 2) (by simp) with h12033 | h12033
                            · linarith only [h0, h12033, hlam]
                            · rcases p12014_3 (m.d 0 3) (by simp) with h12035 | h12035
                              · linarith only [h1, h12035, hlam]
                              · rcases p12014_3 (m.d 0 4) (by simp) with h12037 | h12037
                                · linarith only [h12037, h2, hlam]
                                · rcases p12014_3 (m.d 0 5) (by simp) with h12039 | h12039
                                  · linarith only [h12039, h3, hlam]
                                  · rcases h2bigk with h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c | h12041c
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h12011, h8360, hc12, hc23, hlam, hphi, p12041_1]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h4, hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h7337, hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h8360, hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h0, hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h11852, hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h11854, hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h11856, hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h11862, hc02, hc34, hlam, hphi, ht23, p12041_1]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h11862, hc12, hc34, hlam, hphi, ht23, p12041_1]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h11862, hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h0, h11862, h8360, hc12, hc34, hlam, hphi, ht23, p12041_1]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      rcases p12041_3 (m.d 0 2) (by simp) with h12057 | h12057
                                      · linarith only [h12057, hlam, p12041_0]
                                      · rcases p12041_3 (m.d 1 2) (by simp) with h12059 | h12059
                                        · linarith only [h11854, h12059, hlam]
                                        · rcases p12041_3 (m.d 2 3) (by simp) with h12061 | h12061
                                          · linarith only [h11862, h12061, hlam]
                                          · linarith only [h12061, h4, hlam]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      rcases p12041_3 (m.d 0 2) (by simp) with h12064 | h12064
                                      · linarith only [h12064, h7337, hlam]
                                      · linarith only [h0, h12064, hlam]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h0, h11862, h4, hc12, hc34, hlam, hphi, ht23, p12041_1]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h0, h11862, h8360, hc12, hc34, hlam, hphi, ht23, p12041_1]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h0, h11862, h12011, hc12, hc34, hlam, hphi, ht23, p12041_1]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h11862, h12011, hc12, hc34, hlam, hphi, ht23, p12041_1]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h12011, hlam, p12041_1]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [h12012, hlam, p12041_0]
                                    · have p12041_0 := h12041c.1
                                      have p12041_1 := h12041c.2.1
                                      have p12041_2 := h12041c.2.2.1
                                      have p12041_3 := h12041c.2.2.2
                                      linarith only [hlam, p12041_0]
                          · linarith only [h12032, h2, hlam]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          rcases p12014_3 (m.d 0 1) (by simp) with h12076 | h12076
                          · rcases p12014_3 (m.d 0 2) (by simp) with h12077 | h12077
                            · linarith only [h0, h12077, hlam]
                            · rcases p12014_3 (m.d 0 3) (by simp) with h12079 | h12079
                              · linarith only [h1, h12079, hlam]
                              · linarith only [h11850, h12079, hlam]
                          · linarith only [h12076, h3, hlam]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h0, hlam, p12014_0]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [hlam, p12014_0]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h4, hlam, p12014_0]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h7337, hlam, p12014_1]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h8360, hlam, p12014_0]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h1, hlam, p12014_1]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h0, h11862, h4, hc12, hc34, hlam, hphi, ht23, p12014_1]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [hlam, p12014_0]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h9250, hlam, p12014_1]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h0, h11862, h4, h8360, hc12, hc34, hlam, hphi, ht23, p12014_1]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h2, hlam, p12014_0]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          rcases p12014_3 (m.d 0 1) (by simp) with h12094 | h12094
                          · rcases p12014_3 (m.d 0 2) (by simp) with h12095 | h12095
                            · linarith only [h12095, h7337, hlam]
                            · rcases p12014_3 (m.d 0 3) (by simp) with h12097 | h12097
                              · linarith only [h12097, h9250, hlam]
                              · linarith only [h12097, h4, hlam]
                          · linarith only [h0, h12094, hlam]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          rcases p12014_3 (m.d 0 1) (by simp) with h12101 | h12101
                          · rcases p12014_3 (m.d 0 2) (by simp) with h12102 | h12102
                            · linarith only [h12102, h7337, hlam]
                            · rcases p12014_3 (m.d 0 3) (by simp) with h12104 | h12104
                              · linarith only [h12104, h9250, hlam]
                              · rcases p12014_3 (m.d 0 4) (by simp) with h12106 | h12106
                                · rcases p12014_3 (m.d 0 5) (by simp) with h12107 | h12107
                                  · linarith only [h11851, h12107, hlam]
                                  · rcases h2bigk with h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c | h12109c
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h11862, h4, hc12, hc34, hlam, hphi, ht23, p12109_1]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h4, hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h7337, hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h8360, hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h0, hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h11852, hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h11854, hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h11856, hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h11862, hc02, hc34, hlam, hphi, ht23, p12109_1]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h11862, hc12, hc34, hlam, hphi, ht23, p12109_1]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h11862, hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h0, h11862, h8360, hc12, hc34, hlam, hphi, ht23, p12109_1]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      rcases p12109_3 (m.d 0 2) (by simp) with h12125 | h12125
                                      · linarith only [h12125, hlam, p12109_0]
                                      · rcases p12109_3 (m.d 1 2) (by simp) with h12127 | h12127
                                        · linarith only [h11854, h12127, hlam]
                                        · rcases p12109_3 (m.d 2 3) (by simp) with h12129 | h12129
                                          · linarith only [h11862, h12129, hlam]
                                          · linarith only [h12129, h4, hlam]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      rcases p12109_3 (m.d 0 2) (by simp) with h12132 | h12132
                                      · linarith only [h12132, h7337, hlam]
                                      · linarith only [h0, h12132, hlam]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h0, h11862, h4, hc12, hc34, hlam, hphi, ht23, p12109_1]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h0, h11862, h8360, hc12, hc34, hlam, hphi, ht23, p12109_1]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h0, h11862, h12011, hc12, hc34, hlam, hphi, ht23, p12109_1]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h11862, h12011, hc12, hc34, hlam, hphi, ht23, p12109_1]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h12011, hlam, p12109_1]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [h12012, hlam, p12109_0]
                                    · have p12109_0 := h12109c.1
                                      have p12109_1 := h12109c.2.1
                                      have p12109_2 := h12109c.2.2.1
                                      have p12109_3 := h12109c.2.2.2
                                      linarith only [hlam, p12109_0]
                                · linarith only [h12106, h9250, hlam]
                          · linarith only [h1, h12101, hlam]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [hlam, p12014_0]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          rcases p12014_3 (m.d 0 1) (by simp) with h12146 | h12146
                          · rcases p12014_3 (m.d 0 2) (by simp) with h12147 | h12147
                            · linarith only [h12147, h7337, hlam]
                            · rcases p12014_3 (m.d 0 3) (by simp) with h12149 | h12149
                              · linarith only [h12149, h9250, hlam]
                              · linarith only [h11850, h12149, hlam]
                          · linarith only [h12146, h3, hlam]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h3, hlam, p12014_0]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h0, h11862, h12011, h8360, hc12, hc34, hlam, hphi, ht23, p12014_1]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h11850, hlam, p12014_0]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [h11851, hlam, p12014_1]
                        · have p12014_0 := h12014c.1
                          have p12014_1 := h12014c.2.1
                          have p12014_2 := h12014c.2.2.1
                          have p12014_3 := h12014c.2.2.2
                          linarith only [hlam, p12014_0]
                      · linarith only [h0, h11862, h12013, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h11851, h12012, h7337, hlam]
                  · linarith only [h0, h1, h11860, h12011, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h11858, h11860, h11861, hlam]
            · linarith only [h11850, h11860, h9250, hc13, hc34, hlam, hphi]
  · linarith only [h11850, h11851, h9250, hlam]

end R2N4
