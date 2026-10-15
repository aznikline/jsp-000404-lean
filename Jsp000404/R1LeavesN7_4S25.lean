import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S22
import Jsp000404.R1LeavesN7_4S23
import Jsp000404.R1LeavesN7_4S24

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8080000 in
set_option maxHeartbeats 8080000 in
theorem r1l7_11_23_L_I_H_I_s14_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h14856 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h17362 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h17828 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  rcases m.htr 0 3 5 (by decide) (by decide) with h18492 | h18492
  · rcases m.htr 0 4 5 (by decide) (by decide) with h18493 | h18493
    · rcases m.htr 1 2 3 (by decide) (by decide) with h18494 | h18494
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18495 | h18495
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18496 | h18496
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18497 | h18497
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18498 | h18498
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18499 | h18499
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18500 | h18500
                  · linarith only [h17828, h18492, h18494, h18500, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h14856, h18494, h18497, h18500, hc01, hc12, hlam, hphi]
                · linarith only [h12794, h17828, h18492, h18493, h18494, h18497, h18499, hc01, hc12, hlam, hphi]
              · linarith only [h17828, h18497, h18498, hc03, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18505 | h18505
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18506 | h18506
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18507 | h18507
                  · linarith only [h18494, h18497, h18507, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18509 | h18509
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18510 | h18510
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18511 | h18511
                        · rcases h1bigk with h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c | h18512c
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [hlam, p18512_0]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h0, hlam, p18512_0]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h11385, hlam, p18512_0]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h12794, hlam, p18512_0]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h13812, hlam, p18512_0]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            rcases p18512_3 (m.d 0 1) (by simp) with h18518 | h18518
                            · linarith only [h18518, hlam, p18512_0]
                            · rcases p18512_3 (m.d 1 2) (by simp) with h18520 | h18520
                              · rcases p18512_3 (m.d 1 3) (by simp) with h18521 | h18521
                                · linarith only [h18494, h18521, hlam]
                                · linarith only [h11385, h18521, hlam]
                              · linarith only [h18520, hlam, p18512_0]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [hlam, p18512_0]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h11385, hc01, hc12, hlam, hphi, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h12794, hc01, hc12, hlam, hphi, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h18497, hc01, hc34, hlam, hphi, ht12, ht23, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h18494, hlam, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [hlam, p18512_0]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h18497, hlam, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h13812, hc01, hc13, hlam, hphi, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            rcases p18512_3 (m.d 0 1) (by simp) with h18534 | h18534
                            · linarith only [h18534, hlam, p18512_0]
                            · rcases p18512_3 (m.d 1 2) (by simp) with h18536 | h18536
                              · rcases p18512_3 (m.d 1 3) (by simp) with h18537 | h18537
                                · linarith only [h18497, h18537, hlam]
                                · linarith only [h11385, h18537, hlam]
                              · linarith only [h0, h18536, hlam]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h18495, hlam, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h11385, h18497, hc01, hc34, hlam, hphi, ht12, ht23, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [hlam, p18512_0]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h13812, h18497, hc01, hc34, hlam, hphi, ht12, ht23, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h18497, h18505, hc01, hc34, hlam, hphi, ht12, ht23, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h18496, hlam, p18512_1]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h18505, hlam, p18512_0]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [h18506, hlam, p18512_0]
                          · have p18512_0 := h18512c.1
                            have p18512_1 := h18512c.2.1
                            have p18512_2 := h18512c.2.2.1
                            have p18512_3 := h18512c.2.2.2
                            linarith only [hlam, p18512_0]
                        · linarith only [h11385, h18497, h18511, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h11385, h14856, h18492, h18493, h18497, h18507, h18510, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h14856, h18492, h18509, hlam]
                · linarith only [h12794, h17362, h18493, h18506, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h14856, h18492, h18494, h18505, hlam]
          · linarith only [h0, h17362, h18495, h18496, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h14856, h18494, h18495, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18557 | h18557
        · linarith only [h0, h17362, h18494, h18557, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18559 | h18559
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18560 | h18560
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18561 | h18561
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18562 | h18562
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18563 | h18563
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18564 | h18564
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18565 | h18565
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18566 | h18566
                        · rcases h1bigk with h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c | h18567c
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h0, hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h11385, hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h12794, hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h13812, hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h18557, h18563, hc01, hc23, hlam, hphi, ht12, p18567_1]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h18494, hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h18557, hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h13812, h18557, h18563, hc01, hc23, hlam, hphi, ht12, p18567_1]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            rcases p18567_3 (m.d 0 1) (by simp) with h18578 | h18578
                            · linarith only [h18578, hlam, p18567_0]
                            · rcases p18567_3 (m.d 1 2) (by simp) with h18580 | h18580
                              · linarith only [h18494, h18580, hlam]
                              · linarith only [h0, h18580, hlam]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h0, h18494, hc01, hc23, hlam, hphi, ht12, p18567_1]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h13812, h18494, h18557, h18559, hc01, hc23, hlam, hphi, ht12, p18567_1]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h13812, h18494, hc01, hc23, hlam, hphi, ht12, p18567_1]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            rcases p18567_3 (m.d 0 1) (by simp) with h18587 | h18587
                            · linarith only [h18587, hlam, p18567_0]
                            · rcases p18567_3 (m.d 1 2) (by simp) with h18589 | h18589
                              · linarith only [h18557, h18589, hlam]
                              · linarith only [h0, h18589, hlam]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h13812, h18559, hc01, hc14, hlam, hphi, p18567_1]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h18560, hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h13812, h18557, h18563, hc01, hc23, hlam, hphi, ht12, p18567_1]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h18494, h18559, hc01, hc23, hlam, hphi, ht12, p18567_1]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h18559, hlam, p18567_1]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h18561, hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [h18562, hlam, p18567_0]
                          · have p18567_0 := h18567c.1
                            have p18567_1 := h18567c.2.1
                            have p18567_2 := h18567c.2.2.1
                            have p18567_3 := h18567c.2.2.2
                            linarith only [hlam, p18567_0]
                        · linarith only [h17828, h18493, h18566, hlam]
                      · linarith only [h17828, h18492, h18493, h18557, h18565, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h14856, h17828, h18494, h18560, h18564, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h18494, h18560, h18563, hlam]
                · linarith only [h12794, h17828, h18492, h18493, h18560, h18562, hc01, hc13, hlam, hphi]
              · linarith only [h17828, h18492, h18560, h18561, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18607 | h18607
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18608 | h18608
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18609 | h18609
                  · linarith only [h13812, h18494, h18559, h18560, h18609, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h13812, h18494, h18559, h18609, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h12794, h18493, h18608, hlam]
              · linarith only [h11385, h18492, h18607, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18614 | h18614
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18615 | h18615
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18616 | h18616
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18617 | h18617
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18618 | h18618
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18619 | h18619
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18620 | h18620
                        · rcases h1bigk with h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c | h18621c
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h0, hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h11385, hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h12794, hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h13812, hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h18559, h18617, h18619, hc01, hc23, hlam, hphi, ht12, p18621_1]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h18494, hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h18557, hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h18559, hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            rcases p18621_3 (m.d 0 1) (by simp) with h18632 | h18632
                            · linarith only [h18632, hlam, p18621_0]
                            · rcases p18621_3 (m.d 1 2) (by simp) with h18634 | h18634
                              · linarith only [h18494, h18634, hlam]
                              · linarith only [h0, h18634, hlam]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h0, h18494, hc01, hc23, hlam, hphi, ht12, p18621_1]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h12794, h18494, hc01, hc23, hlam, hphi, ht12, p18621_1]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h0, h18494, h18559, hc01, hc23, hlam, hphi, ht12, p18621_1]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            rcases p18621_3 (m.d 0 1) (by simp) with h18641 | h18641
                            · linarith only [h18641, hlam, p18621_0]
                            · rcases p18621_3 (m.d 1 2) (by simp) with h18643 | h18643
                              · linarith only [h18557, h18643, hlam]
                              · linarith only [h0, h18643, hlam]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p18621_1]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h18614, hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h0, h18557, h18559, h18617, hc01, hc23, hlam, hphi, ht12, p18621_1]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            rcases p18621_3 (m.d 0 1) (by simp) with h18650 | h18650
                            · linarith only [h18650, hlam, p18621_0]
                            · rcases p18621_3 (m.d 1 2) (by simp) with h18652 | h18652
                              · linarith only [h18559, h18652, hlam]
                              · linarith only [h0, h18652, hlam]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p18621_1]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h18615, hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [h18616, hlam, p18621_0]
                          · have p18621_0 := h18621c.1
                            have p18621_1 := h18621c.2.1
                            have p18621_2 := h18621c.2.2.1
                            have p18621_3 := h18621c.2.2.2
                            linarith only [hlam, p18621_0]
                        · linarith only [h17828, h18493, h18620, hlam]
                      · linarith only [h12794, h17828, h18492, h18493, h18494, h18557, h18614, h18619, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h17828, h18492, h18494, h18614, h18618, hlam]
                  · linarith only [h18494, h18614, h18617, hlam]
                · linarith only [h17828, h18492, h18493, h18614, h18616, hlam]
              · linarith only [h17828, h18492, h18614, h18615, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18665 | h18665
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18666 | h18666
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18667 | h18667
                  · linarith only [h0, h18559, h18614, h18665, h18667, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h18494, h18667, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h12794, h17828, h18492, h18493, h18666, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h11385, h18492, h18665, hlam]
    · linarith only [h17828, h18492, h18493, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h18673 | h18673
    · rcases m.htr 1 2 3 (by decide) (by decide) with h18674 | h18674
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18675 | h18675
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18676 | h18676
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18677 | h18677
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18678 | h18678
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18679 | h18679
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18680 | h18680
                  · linarith only [h0, h14856, h17828, h18674, h18680, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h14856, h18677, h18680, hc01, hc13, hlam, hphi]
                · linarith only [h12794, h18673, h18679, hlam]
              · linarith only [h0, h14856, h17828, h18677, h18678, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18685 | h18685
              · linarith only [h0, h14856, h18492, h18677, h18685, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18687 | h18687
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18688 | h18688
                  · linarith only [h0, h14856, h17828, h18674, h18688, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18690 | h18690
                    · linarith only [h18674, h18685, h18690, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18692 | h18692
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18693 | h18693
                        · rcases h1bigk with h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c | h18694c
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [hlam, p18694_0]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h0, hlam, p18694_0]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h11385, hlam, p18694_0]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h12794, hlam, p18694_0]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h13812, hlam, p18694_0]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            rcases p18694_3 (m.d 0 1) (by simp) with h18700 | h18700
                            · linarith only [h18700, hlam, p18694_0]
                            · rcases p18694_3 (m.d 1 2) (by simp) with h18702 | h18702
                              · rcases p18694_3 (m.d 1 3) (by simp) with h18703 | h18703
                                · linarith only [h18674, h18703, hlam]
                                · linarith only [h11385, h18703, hlam]
                              · linarith only [h18702, hlam, p18694_0]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [hlam, p18694_0]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h0, h14856, h18674, hc01, hc12, hlam, hphi, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h12794, hc01, hc12, hlam, hphi, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h13812, hc01, hc12, hlam, hphi, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h18685, h18693, hc01, hc34, hlam, hphi, ht12, ht23, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h18674, hlam, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [hlam, p18694_0]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h18677, hlam, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h18685, hlam, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            rcases p18694_3 (m.d 0 1) (by simp) with h18716 | h18716
                            · linarith only [h18716, hlam, p18694_0]
                            · rcases p18694_3 (m.d 1 2) (by simp) with h18718 | h18718
                              · rcases p18694_3 (m.d 1 3) (by simp) with h18719 | h18719
                                · linarith only [h18677, h18719, hlam]
                                · linarith only [h11385, h18719, hlam]
                              · linarith only [h0, h18718, hlam]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h18675, hlam, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h0, h14856, h18674, hc01, hc14, hlam, hphi, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [hlam, p18694_0]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h0, h14856, h18674, h18677, h18685, hc01, hc34, hlam, hphi, ht12, ht23, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            rcases p18694_3 (m.d 0 1) (by simp) with h18727 | h18727
                            · linarith only [h18727, hlam, p18694_0]
                            · rcases p18694_3 (m.d 1 2) (by simp) with h18729 | h18729
                              · rcases p18694_3 (m.d 1 3) (by simp) with h18730 | h18730
                                · linarith only [h18685, h18730, hlam]
                                · linarith only [h11385, h18730, hlam]
                              · linarith only [h0, h18729, hlam]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h18676, hlam, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h0, h14856, h18674, hc01, hc15, hlam, hphi, p18694_1]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [h18687, hlam, p18694_0]
                          · have p18694_0 := h18694c.1
                            have p18694_1 := h18694c.2.1
                            have p18694_2 := h18694c.2.2.1
                            have p18694_3 := h18694c.2.2.2
                            linarith only [hlam, p18694_0]
                        · linarith only [h12794, h17362, h18673, h18677, h18693, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h17362, h18673, h18692, hlam]
                · linarith only [h12794, h17362, h18673, h18675, h18687, hc01, hc12, hlam, hphi]
          · linarith only [h17362, h18675, h18676, hc02, hc25, hlam, hphi]
        · linarith only [h0, h14856, h18674, h18675, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18743 | h18743
        · linarith only [h0, h17362, h18674, h18743, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18745 | h18745
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18746 | h18746
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18747 | h18747
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18748 | h18748
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18749 | h18749
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18750 | h18750
                    · linarith only [h11385, h18492, h18743, h18745, h18749, h18750, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h18743, h18749, h18750, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h14856, h18492, h18674, h18745, h18746, h18747, h18749, hc01, hc13, hlam, hphi]
                · linarith only [h12794, h18673, h18748, hlam]
              · linarith only [h0, h14856, h17828, h18746, h18747, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18756 | h18756
              · linarith only [h0, h14856, h18492, h18746, h18756, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h18674, h18745, h18756, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18759 | h18759
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18760 | h18760
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18761 | h18761
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18762 | h18762
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18763 | h18763
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18764 | h18764
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18765 | h18765
                        · rcases h1bigk with h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c | h18766c
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h0, hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h11385, hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h12794, hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h13812, hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h18745, h18762, h18764, hc01, hc23, hlam, hphi, ht12, p18766_1]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h18674, hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h18743, hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h18745, hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            rcases p18766_3 (m.d 0 1) (by simp) with h18777 | h18777
                            · linarith only [h18777, hlam, p18766_0]
                            · rcases p18766_3 (m.d 1 2) (by simp) with h18779 | h18779
                              · linarith only [h18674, h18779, hlam]
                              · linarith only [h0, h18779, hlam]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h0, hc01, hc13, hlam, hphi, p18766_1]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h0, h18674, h18745, h18761, hc01, hc23, hlam, hphi, ht12, p18766_1]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h0, h18674, h18745, hc01, hc23, hlam, hphi, ht12, p18766_1]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            rcases p18766_3 (m.d 0 1) (by simp) with h18786 | h18786
                            · linarith only [h18786, hlam, p18766_0]
                            · rcases p18766_3 (m.d 1 2) (by simp) with h18788 | h18788
                              · linarith only [h18743, h18788, hlam]
                              · linarith only [h0, h18788, hlam]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p18766_1]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h18759, hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h0, h14856, h18492, h18743, h18760, h18762, hc01, hc23, hlam, hphi, ht12, p18766_1]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            rcases p18766_3 (m.d 0 1) (by simp) with h18795 | h18795
                            · linarith only [h18795, hlam, p18766_0]
                            · rcases p18766_3 (m.d 1 2) (by simp) with h18797 | h18797
                              · linarith only [h18745, h18797, hlam]
                              · linarith only [h0, h18797, hlam]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h0, hc01, hc15, hlam, hphi, p18766_1]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h18760, hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [h18761, hlam, p18766_0]
                          · have p18766_0 := h18766c.1
                            have p18766_1 := h18766c.2.1
                            have p18766_2 := h18766c.2.2.1
                            have p18766_3 := h18766c.2.2.2
                            linarith only [hlam, p18766_0]
                        · linarith only [h0, h12794, h14856, h17828, h18673, h18743, h18762, h18765, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h12794, h17828, h18673, h18743, h18764, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h14856, h17828, h18674, h18759, h18763, hc02, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h14856, h18492, h18674, h18760, h18762, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h12794, h17828, h18673, h18759, h18761, hc01, hc13, hlam, hphi]
              · linarith only [h14856, h17828, h18759, h18760, hc02, hc35, hlam, hphi, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18810 | h18810
              · linarith only [h0, h14856, h18492, h18759, h18810, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18812 | h18812
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18813 | h18813
                  · linarith only [h11385, h18759, h18813, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h18674, h18813, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h12794, h18673, h18812, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h18817 | h18817
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18818 | h18818
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18819 | h18819
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18820 | h18820
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18821 | h18821
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18822 | h18822
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18823 | h18823
                  · linarith only [h0, h14856, h17828, h18817, h18823, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h14856, h18817, h18820, h18823, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18826 | h18826
                  · linarith only [h0, h14856, h17828, h18817, h18826, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h14856, h18817, h18820, h18826, hc01, hc12, hlam, hphi]
              · linarith only [h0, h14856, h17828, h18820, h18821, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18830 | h18830
              · linarith only [h0, h14856, h18492, h18820, h18830, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18832 | h18832
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18833 | h18833
                  · linarith only [h18673, h18817, h18820, h18830, h18832, h18833, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18835 | h18835
                    · linarith only [h11385, h18830, h18833, h18835, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18837 | h18837
                      · linarith only [h0, h14856, h17828, h18673, h18818, h18837, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h17362, h18832, h18837, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18840 | h18840
                  · linarith only [h0, h14856, h17828, h18817, h18840, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18842 | h18842
                    · linarith only [h0, h14856, h18492, h18817, h18820, h18832, h18842, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18844 | h18844
                      · linarith only [h11385, h18820, h18832, h18844, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18846 | h18846
                        · linarith only [h0, h14856, h18817, h18820, h18832, h18846, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h14856, h18817, h18820, h18846, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h14856, h18817, h18819, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h14856, h18817, h18818, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h18851 | h18851
        · linarith only [h0, h17362, h18817, h18851, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h18853 | h18853
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18854 | h18854
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18855 | h18855
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18856 | h18856
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18857 | h18857
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18858 | h18858
                    · linarith only [h0, h14856, h18492, h18851, h18853, h18857, h18858, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h18851, h18857, h18858, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h18817, h18857, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h18851, h18853, h18856, hlam]
              · linarith only [h0, h14856, h17828, h18854, h18855, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18864 | h18864
              · linarith only [h0, h14856, h18492, h18854, h18864, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h18817, h18853, h18864, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18867 | h18867
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18868 | h18868
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18869 | h18869
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18870 | h18870
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18871 | h18871
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18872 | h18872
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18873 | h18873
                        · linarith only [h0, h14856, h17828, h18673, h18867, h18873, hc01, hc13, hlam, hphi]
                        · linarith only [h0, h14856, h17828, h18869, h18873, hc01, hc14, hlam, hphi]
                      · linarith only [h18851, h18869, h18872, hlam]
                    · linarith only [h0, h14856, h17828, h18673, h18851, h18869, h18870, h18871, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h14856, h17828, h18673, h18817, h18867, h18869, h18870, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18879 | h18879
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h18880 | h18880
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18881 | h18881
                      · linarith only [h12794, h18869, h18881, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h18851, h18881, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h18817, h18868, h18880, hlam]
                  · linarith only [h18817, h18867, h18879, hlam]
              · linarith only [h0, h14856, h17828, h18867, h18868, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h18887 | h18887
              · linarith only [h0, h14856, h18492, h18867, h18887, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18889 | h18889
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18890 | h18890
                  · linarith only [h0, h18817, h18867, h18890, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h18817, h18890, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h18893 | h18893
                  · linarith only [h0, h18817, h18867, h18893, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h18817, h18893, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 8080000 in
set_option maxHeartbeats 8080000 in
theorem r1l7_11_23_L_I_H_I_s14_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h14856 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h17362 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  rcases m.htr 0 3 4 (by decide) (by decide) with h17828 | h17828
  · exact r1l7_11_23_L_I_H_I_s14_x1_x1_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 h14856 h17362 h17828
  · exact r1l7_11_23_L_I_H_I_s14_x1_x1_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 h14856 h17362 h17828

set_option maxHeartbeats 8080000 in
set_option maxHeartbeats 8080000 in
theorem r1l7_11_23_L_I_H_I_s14_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h14856 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  rcases m.htr 0 2 4 (by decide) (by decide) with h17362 | h17362
  · exact r1l7_11_23_L_I_H_I_s14_x1_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 h14856 h17362
  · exact r1l7_11_23_L_I_H_I_s14_x1_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 h14856 h17362

set_option maxHeartbeats 8080000 in
set_option maxHeartbeats 8080000 in
theorem r1l7_11_23_L_I_H_I_s14 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  rcases m.htr 0 2 3 (by decide) (by decide) with h14856 | h14856
  · exact r1l7_11_23_L_I_H_I_s14_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 h14856
  · exact r1l7_11_23_L_I_H_I_s14_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 h14856

end R2N4
