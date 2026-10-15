import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S50

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 22740000 in
set_option maxHeartbeats 22740000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h20697 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h20698 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h20699 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h20700 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h20701 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  rcases m.htr 0 3 5 (by decide) (by decide) with h21442 | h21442
  · rcases m.htr 0 4 5 (by decide) (by decide) with h21443 | h21443
    · rcases m.htr 1 2 3 (by decide) (by decide) with h21444 | h21444
      · rcases m.htr 1 2 4 (by decide) (by decide) with h21445 | h21445
        · rcases m.htr 1 2 5 (by decide) (by decide) with h21446 | h21446
          · rcases m.htr 1 3 4 (by decide) (by decide) with h21447 | h21447
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21448 | h21448
              · rcases m.htr 1 4 5 (by decide) (by decide) with h21449 | h21449
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21450 | h21450
                  · linarith only [h20698, h20701, h21450, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h21452 | h21452
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21453 | h21453
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21454 | h21454
                        · rcases h0bigk with h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c | h21455c
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [hlam, p21455_0]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h0, hlam, p21455_1]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h15532, hlam, p21455_0]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h18443, hlam, p21455_1]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h15532, h20701, h21444, h21447, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p21455_1]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            rcases p21455_3 (m.d 0 1) (by simp) with h21461 | h21461
                            · linarith only [h0, h21461, hlam]
                            · rcases p21455_3 (m.d 0 2) (by simp) with h21463 | h21463
                              · rcases p21455_3 (m.d 0 3) (by simp) with h21464 | h21464
                                · linarith only [h20698, h21464, hlam]
                                · linarith only [h15532, h21464, hlam]
                              · linarith only [h0, h21463, hlam]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [hlam, p21455_0]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            rcases p21455_3 (m.d 0 1) (by simp) with h21469 | h21469
                            · linarith only [h0, h21469, hlam]
                            · rcases p21455_3 (m.d 0 2) (by simp) with h21471 | h21471
                              · rcases p21455_3 (m.d 0 3) (by simp) with h21472 | h21472
                                · linarith only [h20698, h21472, hlam]
                                · rcases p21455_3 (m.d 0 4) (by simp) with h21474 | h21474
                                  · linarith only [h20699, h21474, hlam]
                                  · linarith only [h20701, h21474, hlam]
                              · linarith only [h20698, h21471, hlam]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            rcases p21455_3 (m.d 0 1) (by simp) with h21478 | h21478
                            · linarith only [h0, h21478, hlam]
                            · rcases p21455_3 (m.d 0 2) (by simp) with h21480 | h21480
                              · rcases p21455_3 (m.d 0 3) (by simp) with h21481 | h21481
                                · linarith only [h20698, h21481, hlam]
                                · rcases p21455_3 (m.d 0 4) (by simp) with h21483 | h21483
                                  · linarith only [h20699, h21483, hlam]
                                  · rcases p21455_3 (m.d 0 5) (by simp) with h21485 | h21485
                                    · linarith only [h20700, h21485, hlam]
                                    · rcases h2bigk with h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c | h21487c
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h0, hlam, p21487_1]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        rcases p21487_3 (m.d 0 2) (by simp) with h21490 | h21490
                                        · rcases p21487_3 (m.d 1 2) (by simp) with h21491 | h21491
                                          · rcases p21487_3 (m.d 2 3) (by simp) with h21492 | h21492
                                            · linarith only [h21492, hlam, p21487_0]
                                            · rcases p21487_3 (m.d 2 4) (by simp) with h21494 | h21494
                                              · linarith only [h20699, h21494, hlam]
                                              · linarith only [h21450, h21494, hlam]
                                          · linarith only [h21444, h21491, hlam]
                                        · linarith only [h21490, hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        rcases p21487_3 (m.d 0 2) (by simp) with h21499 | h21499
                                        · rcases p21487_3 (m.d 1 2) (by simp) with h21500 | h21500
                                          · rcases p21487_3 (m.d 2 3) (by simp) with h21501 | h21501
                                            · linarith only [h20698, h21501, hlam]
                                            · rcases p21487_3 (m.d 2 4) (by simp) with h21503 | h21503
                                              · linarith only [h21503, hlam, p21487_0]
                                              · rcases p21487_3 (m.d 2 5) (by simp) with h21505 | h21505
                                                · linarith only [h20700, h21505, hlam]
                                                · rcases h3bigk with h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c | h21507c
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h15532, hlam, p21507_1]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h0, h20701, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21455_1, p21507_1]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h20701, hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h0, h20701, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p21455_1, p21507_1]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    rcases p21507_3 (m.d 0 3) (by simp) with h21513 | h21513
                                                    · linarith only [h15532, h21513, hlam]
                                                    · rcases p21507_3 (m.d 1 3) (by simp) with h21515 | h21515
                                                      · rcases p21507_3 (m.d 2 3) (by simp) with h21516 | h21516
                                                        · linarith only [h21444, h21516, hlam]
                                                        · rcases p21507_3 (m.d 3 4) (by simp) with h21518 | h21518
                                                          · linarith only [h21447, h21518, hlam]
                                                          · linarith only [h20701, h21518, hlam]
                                                      · linarith only [h15532, h21515, hlam]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    rcases p21507_3 (m.d 0 3) (by simp) with h21523 | h21523
                                                    · linarith only [h15532, h21523, hlam]
                                                    · linarith only [h20698, h21523, hlam]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h15532, h20701, hc01, hc13, hlam, hphi, p21507_1]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h20698, h20701, h21447, h21452, hlam, p21507_2]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h20698, hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h21444, hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h21450, hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h20698, h20701, hc02, hc35, hlam, hphi, ht0b, ht5b, p21455_1, p21507_1]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h15532, h21447, hc01, hc13, hlam, hphi, p21507_1]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h21447, hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h21444, h21447, h21452, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p21507_1]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    rcases p21507_3 (m.d 0 3) (by simp) with h21537 | h21537
                                                    · linarith only [h20701, h21537, hlam]
                                                    · linarith only [h21442, h21537, hlam]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h21442, hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h21448, hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h21452, hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [h21454, hlam, p21507_0]
                                                  · have p21507_0 := h21507c.1
                                                    have p21507_1 := h21507c.2.1
                                                    have p21507_2 := h21507c.2.2.1
                                                    have p21507_3 := h21507c.2.2.2
                                                    linarith only [hlam, p21507_0]
                                          · linarith only [h21445, h21500, hlam]
                                        · linarith only [h21499, hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h15532, h20697, h20701, h21446, hlam, p21455_1, p21487_2]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h15532, h20697, h20701, h21446, h21452, h21454, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21455_1, p21487_1]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        rcases p21487_3 (m.d 0 2) (by simp) with h21550 | h21550
                                        · linarith only [h0, h21550, hlam]
                                        · linarith only [h20698, h21550, hlam]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        rcases p21487_3 (m.d 0 2) (by simp) with h21553 | h21553
                                        · linarith only [h0, h21553, hlam]
                                        · linarith only [h20699, h21553, hlam]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h0, h15532, h20697, h20701, h21446, hlam, p21455_1, p21487_2]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h20698, hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h21444, hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h21450, hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h20698, h20701, h21452, h21454, hc02, hc45, hlam, hphi, ht0b, ht5b, p21455_1, p21487_1]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h20699, hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h21445, hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h0, h20699, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21455_1, p21487_1]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h0, h20699, h21452, h21454, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21455_1, p21487_1]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h20700, hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h21446, hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h21452, hlam, p21487_1]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [h21453, hlam, p21487_0]
                                      · have p21487_0 := h21487c.1
                                        have p21487_1 := h21487c.2.1
                                        have p21487_2 := h21487c.2.2.1
                                        have p21487_3 := h21487c.2.2.2
                                        linarith only [hlam, p21487_0]
                              · linarith only [h20699, h21480, hlam]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            rcases p21455_3 (m.d 0 1) (by simp) with h21573 | h21573
                            · linarith only [h0, h21573, hlam]
                            · linarith only [h20697, h21573, hlam]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h20697, h20701, h21444, h21446, h21447, h21452, h21454, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21455_1]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h20698, hlam, p21455_1]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [hlam, p21455_0]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h20701, hlam, p21455_1]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h20701, h21444, h21447, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p21455_1]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h20697, h20701, h21444, h21446, h21447, h21452, h21454, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21455_1]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h20699, hlam, p21455_0]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h15532, h20697, h20701, h21444, h21446, h21447, h21452, h21454, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21455_1]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [hlam, p21455_0]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            rcases p21455_3 (m.d 0 1) (by simp) with h21585 | h21585
                            · linarith only [h18443, h21585, hlam]
                            · linarith only [h20697, h21585, hlam]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h20697, hlam, p21455_0]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h20700, hlam, p21455_1]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h21442, hlam, p21455_0]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [h21443, hlam, p21455_1]
                          · have p21455_0 := h21455c.1
                            have p21455_1 := h21455c.2.1
                            have p21455_2 := h21455c.2.2.1
                            have p21455_3 := h21455c.2.2.2
                            linarith only [hlam, p21455_0]
                        · linarith only [h15532, h20697, h20701, h21443, h21446, h21452, h21454, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h15532, h20697, h20701, h21444, h21447, h21449, h21453, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h20701, h21442, h21444, h21447, h21452, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h18443, h21443, h21449, hlam]
              · linarith only [h20701, h21442, h21448, hc13, hc34, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h21598 | h21598
              · rcases m.htr 1 4 5 (by decide) (by decide) with h21599 | h21599
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21600 | h21600
                  · linarith only [h15532, h21447, h21600, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h21602 | h21602
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h21603 | h21603
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21604 | h21604
                        · rcases h0bigk with h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c | h21605c
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [hlam, p21605_0]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h0, hlam, p21605_1]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h15532, hlam, p21605_0]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h18443, hlam, p21605_1]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h15532, h20697, h21446, h21447, h21602, h21604, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21605_1]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            rcases p21605_3 (m.d 0 1) (by simp) with h21611 | h21611
                            · linarith only [h0, h21611, hlam]
                            · rcases p21605_3 (m.d 0 2) (by simp) with h21613 | h21613
                              · rcases p21605_3 (m.d 0 3) (by simp) with h21614 | h21614
                                · linarith only [h20698, h21614, hlam]
                                · linarith only [h15532, h21614, hlam]
                              · linarith only [h0, h21613, hlam]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [hlam, p21605_0]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            rcases p21605_3 (m.d 0 1) (by simp) with h21619 | h21619
                            · linarith only [h0, h21619, hlam]
                            · rcases p21605_3 (m.d 0 2) (by simp) with h21621 | h21621
                              · rcases p21605_3 (m.d 0 3) (by simp) with h21622 | h21622
                                · linarith only [h20698, h21622, hlam]
                                · rcases p21605_3 (m.d 0 4) (by simp) with h21624 | h21624
                                  · linarith only [h20699, h21624, hlam]
                                  · linarith only [h20701, h21624, hlam]
                              · linarith only [h20698, h21621, hlam]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            rcases p21605_3 (m.d 0 1) (by simp) with h21628 | h21628
                            · linarith only [h0, h21628, hlam]
                            · rcases p21605_3 (m.d 0 2) (by simp) with h21630 | h21630
                              · rcases p21605_3 (m.d 0 3) (by simp) with h21631 | h21631
                                · linarith only [h20698, h21631, hlam]
                                · rcases p21605_3 (m.d 0 4) (by simp) with h21633 | h21633
                                  · linarith only [h20699, h21633, hlam]
                                  · rcases p21605_3 (m.d 0 5) (by simp) with h21635 | h21635
                                    · linarith only [h20700, h21635, hlam]
                                    · rcases h2bigk with h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c | h21637c
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h0, hlam, p21637_1]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        rcases p21637_3 (m.d 0 2) (by simp) with h21640 | h21640
                                        · rcases p21637_3 (m.d 1 2) (by simp) with h21641 | h21641
                                          · rcases p21637_3 (m.d 2 3) (by simp) with h21642 | h21642
                                            · linarith only [h21642, hlam, p21637_0]
                                            · rcases p21637_3 (m.d 2 4) (by simp) with h21644 | h21644
                                              · linarith only [h20699, h21644, hlam]
                                              · linarith only [h21600, h21644, hlam]
                                          · linarith only [h21444, h21641, hlam]
                                        · linarith only [h21640, hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        rcases p21637_3 (m.d 0 2) (by simp) with h21649 | h21649
                                        · rcases p21637_3 (m.d 1 2) (by simp) with h21650 | h21650
                                          · rcases p21637_3 (m.d 2 3) (by simp) with h21651 | h21651
                                            · linarith only [h20698, h21651, hlam]
                                            · rcases p21637_3 (m.d 2 4) (by simp) with h21653 | h21653
                                              · linarith only [h21653, hlam, p21637_0]
                                              · rcases p21637_3 (m.d 2 5) (by simp) with h21655 | h21655
                                                · linarith only [h20700, h21655, hlam]
                                                · rcases h3bigk with h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c | h21657c
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h15532, hlam, p21657_1]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h0, h20701, h21602, h21604, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21605_1, p21657_1]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h20701, hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h0, h20701, h21604, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21605_1, p21657_1]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h15532, h21447, hc01, hc34, hlam, hphi, ht12, ht23, p21657_1]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h21447, h21602, h21604, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21657_1]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h21447, hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    rcases p21657_3 (m.d 0 3) (by simp) with h21667 | h21667
                                                    · linarith only [h15532, h21667, hlam]
                                                    · linarith only [h21442, h21667, hlam]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h20698, hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h21444, hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h21600, hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h0, h21600, h21604, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21637_1, p21657_1]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    rcases p21657_3 (m.d 0 3) (by simp) with h21675 | h21675
                                                    · linarith only [h21675, hlam, p21657_0]
                                                    · rcases p21657_3 (m.d 1 3) (by simp) with h21677 | h21677
                                                      · linarith only [h21447, h21677, hlam]
                                                      · linarith only [h15532, h21677, hlam]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h15532, h20697, h21446, h21602, h21604, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21657_1]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    rcases p21657_3 (m.d 0 3) (by simp) with h21681 | h21681
                                                    · linarith only [h20701, h21681, hlam]
                                                    · linarith only [h20698, h21681, hlam]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h15532, h20697, h21446, h21447, h21602, hlam, p21657_2]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h21442, hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h21598, hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h21602, hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [h21604, hlam, p21657_0]
                                                  · have p21657_0 := h21657c.1
                                                    have p21657_1 := h21657c.2.1
                                                    have p21657_2 := h21657c.2.2.1
                                                    have p21657_3 := h21657c.2.2.2
                                                    linarith only [hlam, p21657_0]
                                          · linarith only [h21445, h21650, hlam]
                                        · linarith only [h21649, hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h18443, h20697, h21446, hlam, p21605_1, p21637_2]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p21605_1, p21637_1]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        rcases p21637_3 (m.d 0 2) (by simp) with h21696 | h21696
                                        · linarith only [h0, h21696, hlam]
                                        · linarith only [h20698, h21696, hlam]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        rcases p21637_3 (m.d 0 2) (by simp) with h21699 | h21699
                                        · linarith only [h0, h21699, hlam]
                                        · linarith only [h20699, h21699, hlam]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h0, h15532, h20697, h20701, h21446, hlam, p21605_1, p21637_2]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h20698, hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h21444, hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h21600, hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h20698, h20701, h21602, h21604, hc02, hc45, hlam, hphi, ht0b, ht5b, p21605_1, p21637_1]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h20699, hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h21445, hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h0, h15532, h20697, h20699, h21446, h21447, h21602, h21604, hc12, hc23, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p21605_1, p21637_1]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h0, h20699, h21602, h21604, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21605_1, p21637_1]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h20700, hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h21446, hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h21602, hlam, p21637_1]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [h21603, hlam, p21637_0]
                                      · have p21637_0 := h21637c.1
                                        have p21637_1 := h21637c.2.1
                                        have p21637_2 := h21637c.2.2.1
                                        have p21637_3 := h21637c.2.2.2
                                        linarith only [hlam, p21637_0]
                              · linarith only [h20699, h21630, hlam]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            rcases p21605_3 (m.d 0 1) (by simp) with h21719 | h21719
                            · linarith only [h0, h21719, hlam]
                            · linarith only [h20697, h21719, hlam]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h15532, h20697, h21446, h21447, h21602, h21604, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21605_1]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h20698, hlam, p21605_1]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [hlam, p21605_0]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h20701, hlam, p21605_1]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            rcases p21605_3 (m.d 0 1) (by simp) with h21726 | h21726
                            · linarith only [h15532, h21726, hlam]
                            · linarith only [h20697, h21726, hlam]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            rcases p21605_3 (m.d 0 1) (by simp) with h21729 | h21729
                            · linarith only [h18443, h21729, hlam]
                            · rcases p21605_3 (m.d 0 2) (by simp) with h21731 | h21731
                              · rcases p21605_3 (m.d 0 3) (by simp) with h21732 | h21732
                                · linarith only [h20701, h21732, hlam]
                                · linarith only [h15532, h21732, hlam]
                              · linarith only [h0, h21731, hlam]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h20699, hlam, p21605_0]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            rcases p21605_3 (m.d 0 1) (by simp) with h21737 | h21737
                            · linarith only [h18443, h21737, hlam]
                            · rcases p21605_3 (m.d 0 2) (by simp) with h21739 | h21739
                              · rcases p21605_3 (m.d 0 3) (by simp) with h21740 | h21740
                                · linarith only [h20701, h21740, hlam]
                                · rcases p21605_3 (m.d 0 4) (by simp) with h21742 | h21742
                                  · rcases p21605_3 (m.d 0 5) (by simp) with h21743 | h21743
                                    · linarith only [h21443, h21743, hlam]
                                    · rcases h2bigk with h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c | h21745c
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h0, hlam, p21745_1]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        rcases p21745_3 (m.d 0 2) (by simp) with h21748 | h21748
                                        · rcases p21745_3 (m.d 1 2) (by simp) with h21749 | h21749
                                          · rcases p21745_3 (m.d 2 3) (by simp) with h21750 | h21750
                                            · linarith only [h21750, hlam, p21745_0]
                                            · rcases p21745_3 (m.d 2 4) (by simp) with h21752 | h21752
                                              · linarith only [h20699, h21752, hlam]
                                              · linarith only [h21600, h21752, hlam]
                                          · linarith only [h21444, h21749, hlam]
                                        · linarith only [h21748, hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        rcases p21745_3 (m.d 0 2) (by simp) with h21757 | h21757
                                        · rcases p21745_3 (m.d 1 2) (by simp) with h21758 | h21758
                                          · rcases p21745_3 (m.d 2 3) (by simp) with h21759 | h21759
                                            · linarith only [h20698, h21759, hlam]
                                            · rcases p21745_3 (m.d 2 4) (by simp) with h21761 | h21761
                                              · linarith only [h21761, hlam, p21745_0]
                                              · rcases p21745_3 (m.d 2 5) (by simp) with h21763 | h21763
                                                · linarith only [h20700, h21763, hlam]
                                                · rcases h3bigk with h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c | h21765c
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h15532, hlam, p21765_1]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h18443, h21447, h21602, h21604, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21605_1, p21765_1]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h20701, hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h18443, h21447, h21604, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21605_1, p21765_1]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h21447, hc03, hc34, hlam, hphi, p21765_1]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h21447, h21602, h21604, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21765_1]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h21447, hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    rcases p21765_3 (m.d 0 3) (by simp) with h21775 | h21775
                                                    · linarith only [h15532, h21775, hlam]
                                                    · linarith only [h21442, h21775, hlam]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h20698, hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h21444, hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h21600, hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h18443, h20698, h21447, h21604, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21605_1, p21765_1]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    rcases p21765_3 (m.d 0 3) (by simp) with h21783 | h21783
                                                    · linarith only [h21783, hlam, p21765_0]
                                                    · rcases p21765_3 (m.d 1 3) (by simp) with h21785 | h21785
                                                      · linarith only [h21447, h21785, hlam]
                                                      · linarith only [h15532, h21785, hlam]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h15532, h20697, h21446, h21602, h21604, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21765_1]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    rcases p21765_3 (m.d 0 3) (by simp) with h21789 | h21789
                                                    · linarith only [h20701, h21789, hlam]
                                                    · linarith only [h20698, h21789, hlam]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h15532, h18443, h20697, h21446, h21447, h21602, hlam, p21605_1, p21765_2]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h21442, hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h21598, hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h21602, hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [h21604, hlam, p21765_0]
                                                  · have p21765_0 := h21765c.1
                                                    have p21765_1 := h21765c.2.1
                                                    have p21765_2 := h21765c.2.2.1
                                                    have p21765_3 := h21765c.2.2.2
                                                    linarith only [hlam, p21765_0]
                                          · linarith only [h21445, h21758, hlam]
                                        · linarith only [h21757, hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h15532, h20697, h20699, h21446, hlam, p21605_1, p21745_2]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h15532, h20697, h20699, h21446, h21602, h21604, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21605_1, p21745_1]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        rcases p21745_3 (m.d 0 2) (by simp) with h21804 | h21804
                                        · linarith only [h0, h21804, hlam]
                                        · linarith only [h20698, h21804, hlam]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        rcases p21745_3 (m.d 0 2) (by simp) with h21807 | h21807
                                        · linarith only [h0, h21807, hlam]
                                        · linarith only [h20699, h21807, hlam]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h0, h15532, h20697, h20699, h21446, hlam, p21605_1, p21745_2]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h20698, hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h21444, hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h21600, hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h18443, h20698, h21447, h21602, h21604, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21605_1, p21745_1]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h20699, hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h21445, hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h0, h20699, h21602, h21604, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21745_1]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        rcases p21745_3 (m.d 0 2) (by simp) with h21820 | h21820
                                        · rcases p21745_3 (m.d 1 2) (by simp) with h21821 | h21821
                                          · rcases p21745_3 (m.d 2 3) (by simp) with h21822 | h21822
                                            · linarith only [h21600, h21822, hlam]
                                            · linarith only [h21602, h21822, hlam]
                                          · linarith only [h21446, h21821, hlam]
                                        · linarith only [h20700, h21820, hlam]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h20700, hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h21446, hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h21602, hlam, p21745_1]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [h21603, hlam, p21745_0]
                                      · have p21745_0 := h21745c.1
                                        have p21745_1 := h21745c.2.1
                                        have p21745_2 := h21745c.2.2.1
                                        have p21745_3 := h21745c.2.2.2
                                        linarith only [hlam, p21745_0]
                                  · linarith only [h20701, h21742, hlam]
                              · linarith only [h20698, h21739, hlam]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [hlam, p21605_0]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            rcases p21605_3 (m.d 0 1) (by simp) with h21835 | h21835
                            · linarith only [h18443, h21835, hlam]
                            · linarith only [h20697, h21835, hlam]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h20697, hlam, p21605_0]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h20700, hlam, p21605_1]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h21442, hlam, p21605_0]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [h21443, hlam, p21605_1]
                          · have p21605_0 := h21605c.1
                            have p21605_1 := h21605c.2.1
                            have p21605_2 := h21605c.2.2.1
                            have p21605_3 := h21605c.2.2.2
                            linarith only [hlam, p21605_0]
                        · linarith only [h18443, h21443, h21447, h21604, hlam]
                      · linarith only [h15532, h20697, h21447, h21599, h21603, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h15532, h21442, h21447, h21602, hc23, hc34, hlam, hphi]
                · linarith only [h18443, h21443, h21599, hlam]
              · linarith only [h15532, h18443, h20701, h21442, h21598, hc01, hc14, hlam, hphi]
          · linarith only [h0, h20700, h21446, hlam]
        · linarith only [h0, h20699, h21445, hlam]
      · linarith only [h0, h20698, h21444, hlam]
    · linarith only [h15532, h20697, h20701, h21443, hlam]
  · linarith only [h15532, h20697, h21442, hlam]

set_option maxHeartbeats 22740000 in
set_option maxHeartbeats 22740000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h20697 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h20698 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h20699 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h20700 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  rcases m.htr 0 3 4 (by decide) (by decide) with h20701 | h20701
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 h20697 h20698 h20699 h20700 h20701
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 h20697 h20698 h20699 h20700 h20701

set_option maxHeartbeats 22740000 in
set_option maxHeartbeats 22740000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h20697 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h20698 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h20699 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h20700 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  linarith only [h0, h20697, h20700, hlam]

set_option maxHeartbeats 22740000 in
set_option maxHeartbeats 22740000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h20697 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h20698 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h20699 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  rcases m.htr 0 2 5 (by decide) (by decide) with h20700 | h20700
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 h20697 h20698 h20699 h20700
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 h20697 h20698 h20699 h20700

set_option maxHeartbeats 22740000 in
set_option maxHeartbeats 22740000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h20697 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h20698 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h20699 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  rcases m.htr 0 2 5 (by decide) (by decide) with h21854 | h21854
  · rcases m.htr 0 3 4 (by decide) (by decide) with h21855 | h21855
    · linarith only [h20698, h20699, h21855, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h21857 | h21857
      · rcases m.htr 0 4 5 (by decide) (by decide) with h21858 | h21858
        · rcases m.htr 1 2 3 (by decide) (by decide) with h21859 | h21859
          · rcases m.htr 1 2 4 (by decide) (by decide) with h21860 | h21860
            · rcases m.htr 1 2 5 (by decide) (by decide) with h21861 | h21861
              · rcases m.htr 1 3 4 (by decide) (by decide) with h21862 | h21862
                · rcases m.htr 1 3 5 (by decide) (by decide) with h21863 | h21863
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h21864 | h21864
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21865 | h21865
                      · linarith only [h15532, h20698, h20699, h21855, h21860, h21865, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h21867 | h21867
                        · linarith only [h20698, h20699, h21859, h21862, h21865, h21867, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h20698, h20699, h21857, h21859, h21862, h21865, h21867, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h18443, h20697, h21858, h21861, h21864, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h20698, h20699, h21855, h21862, h21863, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h21872 | h21872
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h21873 | h21873
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21874 | h21874
                      · linarith only [h20698, h20699, h21860, h21862, h21874, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h21876 | h21876
                        · linarith only [h20698, h20699, h21860, h21876, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h20698, h20699, h21857, h21860, h21876, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h18443, h20697, h21858, h21861, h21873, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h15532, h20697, h20698, h20699, h21857, h21860, h21861, h21872, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h20699, h21860, h21861, hc02, hc25, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h21882 | h21882
              · rcases m.htr 1 3 4 (by decide) (by decide) with h21883 | h21883
                · linarith only [h15532, h21855, h21859, h21860, h21883, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h21885 | h21885
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h21886 | h21886
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21887 | h21887
                      · linarith only [h0, h20698, h21860, h21883, h21887, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h21889 | h21889
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h21890 | h21890
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h21891 | h21891
                            · rcases h0bigk with h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c | h21892c
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [hlam, p21892_0]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h0, hlam, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h15532, hlam, p21892_0]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h18443, hlam, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h0, h21860, h21887, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h0, h21860, h21887, hc01, hc34, hlam, hphi, ht12, ht23, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [hlam, p21892_0]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h0, h21860, h21887, hc03, hc34, hlam, hphi, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h20699, hlam, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                rcases p21892_3 (m.d 0 1) (by simp) with h21902 | h21902
                                · linarith only [h0, h21902, hlam]
                                · linarith only [h20697, h21902, hlam]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h0, h20697, h20698, h21860, h21882, h21887, h21889, h21891, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h20698, hlam, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [hlam, p21892_0]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h21855, hlam, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                rcases p21892_3 (m.d 0 1) (by simp) with h21909 | h21909
                                · linarith only [h15532, h21909, hlam]
                                · linarith only [h20697, h21909, hlam]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                rcases p21892_3 (m.d 0 1) (by simp) with h21912 | h21912
                                · linarith only [h18443, h21912, hlam]
                                · rcases p21892_3 (m.d 0 2) (by simp) with h21914 | h21914
                                  · linarith only [h20699, h21914, hlam]
                                  · linarith only [h0, h21914, hlam]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h20698, h20699, h21887, hc23, hc34, hlam, hphi, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                rcases p21892_3 (m.d 0 1) (by simp) with h21918 | h21918
                                · linarith only [h18443, h21918, hlam]
                                · rcases p21892_3 (m.d 0 2) (by simp) with h21920 | h21920
                                  · linarith only [h20699, h21920, hlam]
                                  · linarith only [h20698, h21920, hlam]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [hlam, p21892_0]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                rcases p21892_3 (m.d 0 1) (by simp) with h21924 | h21924
                                · linarith only [h18443, h21924, hlam]
                                · linarith only [h20697, h21924, hlam]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h20697, hlam, p21892_0]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h21854, hlam, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h21857, hlam, p21892_0]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [h21858, hlam, p21892_1]
                              · have p21892_0 := h21892c.1
                                have p21892_1 := h21892c.2.1
                                have p21892_2 := h21892c.2.2.1
                                have p21892_3 := h21892c.2.2.2
                                linarith only [hlam, p21892_0]
                            · linarith only [h20698, h20699, h21887, h21889, h21891, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h15532, h20697, h21859, h21860, h21886, h21890, hlam]
                        · linarith only [h15532, h21857, h21859, h21860, h21887, h21889, hc23, hc34, hlam, hphi]
                    · linarith only [h18443, h21858, h21886, hlam]
                  · linarith only [h15532, h21857, h21885, hlam]
              · linarith only [h15532, h20697, h21854, h21859, h21882, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h20698, h21859, hlam]
        · linarith only [h0, h20697, h20699, h21858, hlam]
      · linarith only [h15532, h20697, h21857, hlam]
  · linarith only [h0, h20697, h21854, hlam]

set_option maxHeartbeats 22740000 in
set_option maxHeartbeats 22740000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h20697 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h20698 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  rcases m.htr 0 2 4 (by decide) (by decide) with h20699 | h20699
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 h20697 h20698 h20699
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 h20697 h20698 h20699

end R2N4
