import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S62
import Jsp000404.R1LeavesN7_0S70
import Jsp000404.R1LeavesN7_0S85
import Jsp000404.R1LeavesN7_0S89

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h36830 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  rcases m.htr 0 2 4 (by decide) (by decide) with h38457 | h38457
  · rcases m.htr 0 2 5 (by decide) (by decide) with h38458 | h38458
    · rcases m.htr 0 3 4 (by decide) (by decide) with h38459 | h38459
      · rcases m.htr 0 3 5 (by decide) (by decide) with h38460 | h38460
        · rcases m.htr 0 4 5 (by decide) (by decide) with h38461 | h38461
          · rcases m.htr 1 2 3 (by decide) (by decide) with h38462 | h38462
            · rcases m.htr 1 2 4 (by decide) (by decide) with h38463 | h38463
              · rcases m.htr 1 2 5 (by decide) (by decide) with h38464 | h38464
                · rcases m.htr 1 3 4 (by decide) (by decide) with h38465 | h38465
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h38466 | h38466
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h38467 | h38467
                      · linarith only [h0, h36828, h36830, h38462, h38467, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h36828, h36830, h38461, h38462, h38467, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h36829, h36830, h38460, h38462, h38466, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h33187, h36828, h38459, h38463, h38465, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h36828, h36830, h38462, h38463, h38464, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h36830, h38462, h38463, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h38474 | h38474
              · rcases m.htr 1 2 5 (by decide) (by decide) with h38475 | h38475
                · rcases m.htr 1 3 4 (by decide) (by decide) with h38476 | h38476
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h38477 | h38477
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h38478 | h38478
                      · linarith only [h0, h36828, h38462, h38478, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h36828, h38461, h38462, h38478, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h33187, h36829, h38460, h38477, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h33187, h36829, h38459, h38476, hc03, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h36828, h38458, h38474, h38475, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h38457, h38474, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h38485 | h38485
            · rcases m.htr 1 2 4 (by decide) (by decide) with h38486 | h38486
              · rcases m.htr 1 2 5 (by decide) (by decide) with h38487 | h38487
                · rcases m.htr 1 3 4 (by decide) (by decide) with h38488 | h38488
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h38489 | h38489
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h38490 | h38490
                      · linarith only [h0, h36828, h36830, h38461, h38485, h38490, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h38492 | h38492
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h38493 | h38493
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h38494 | h38494
                            · linarith only [h36828, h38461, h38486, h38494, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h38496 | h38496
                              · linarith only [h36828, h38461, h38486, h38492, h38496, hlam]
                              · rcases h1bigk with h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c | h38498c
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h0, hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h33187, hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h0, h36830, h38485, h38486, h38492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38498_1]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h0, h36830, h38485, h38486, h38490, h38492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38498_1]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  rcases p38498_3 (m.d 0 1) (by simp) with h38504 | h38504
                                  · linarith only [h38504, hlam, p38498_0]
                                  · rcases p38498_3 (m.d 1 2) (by simp) with h38506 | h38506
                                    · rcases p38498_3 (m.d 1 3) (by simp) with h38507 | h38507
                                      · linarith only [h38485, h38507, hlam]
                                      · linarith only [h33187, h38507, hlam]
                                    · linarith only [h38506, hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h33187, hc01, hc12, hlam, hphi, p38498_1]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h0, h36829, h36830, h38485, h38490, hlam, p38498_2]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h0, h36829, h36830, h38485, hlam, p38498_2]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  rcases p38498_3 (m.d 0 1) (by simp) with h38515 | h38515
                                  · linarith only [h38515, hlam, p38498_0]
                                  · rcases p38498_3 (m.d 1 2) (by simp) with h38517 | h38517
                                    · rcases p38498_3 (m.d 1 3) (by simp) with h38518 | h38518
                                      · rcases p38498_3 (m.d 1 4) (by simp) with h38519 | h38519
                                        · linarith only [h38488, h38519, hlam]
                                        · rcases p38498_3 (m.d 1 5) (by simp) with h38521 | h38521
                                          · linarith only [h38489, h38521, hlam]
                                          · rcases h1emax with h38523 | h38523 | h38523 | h38523 | h38523
                                            · rcases h2bigk with h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c | h38524c
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h0, hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h36830, hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h36830, h38485, h38492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38524_1]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h36830, h38485, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p38524_1]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                rcases p38524_3 (m.d 0 2) (by simp) with h38530 | h38530
                                                · linarith only [h0, h38530, hlam]
                                                · rcases p38524_3 (m.d 1 2) (by simp) with h38532 | h38532
                                                  · rcases p38524_3 (m.d 2 3) (by simp) with h38533 | h38533
                                                    · linarith only [h38485, h38533, hlam]
                                                    · linarith only [h36830, h38533, hlam]
                                                  · linarith only [h0, h38532, hlam]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h0, h36829, h36830, h38486, h38490, h38492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38524_1]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h0, h36829, h36830, h38485, h38486, h38490, hlam, p38524_2]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h36830, h38458, h38485, hlam, p38524_2]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h0, h36829, h38485, h38486, h38490, h38492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38524_1]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h38485, hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                rcases p38524_3 (m.d 0 2) (by simp) with h38544 | h38544
                                                · linarith only [h36830, h38544, hlam]
                                                · linarith only [h38457, h38544, hlam]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                rcases p38524_3 (m.d 0 2) (by simp) with h38547 | h38547
                                                · linarith only [h36830, h38547, hlam]
                                                · linarith only [h38458, h38547, hlam]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h38457, hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h38486, hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h38492, hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h38494, hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h38458, hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h38487, hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h38493, hlam, p38524_0]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [h36829, h38487, h38492, h38523, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38524_1]
                                              · have p38524_0 := h38524c.1
                                                have p38524_1 := h38524c.2.1
                                                have p38524_2 := h38524c.2.2.1
                                                have p38524_3 := h38524c.2.2.2
                                                linarith only [hlam, p38524_0]
                                            · linarith only [h0, h36830, h38485, h38523, hc01, hlam]
                                            · linarith only [h36829, h38486, h38490, h38492, h38523, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38498_1]
                                            · rcases h2bigk with h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c | h38562c
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h0, hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h36830, hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h36830, h38485, h38492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38562_1]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h36830, h38485, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p38562_1]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                rcases p38562_3 (m.d 0 2) (by simp) with h38568 | h38568
                                                · linarith only [h0, h38568, hlam]
                                                · rcases p38562_3 (m.d 1 2) (by simp) with h38570 | h38570
                                                  · rcases p38562_3 (m.d 2 3) (by simp) with h38571 | h38571
                                                    · linarith only [h38485, h38571, hlam]
                                                    · linarith only [h36830, h38571, hlam]
                                                  · linarith only [h0, h38570, hlam]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h0, h36829, h36830, h38486, h38490, h38492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38562_1]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h0, h36829, h36830, h38485, h38486, h38490, hlam, p38562_2]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h36830, h38458, h38485, hlam, p38562_2]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h0, h36829, h38485, h38486, h38490, h38492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38562_1]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h38485, hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                rcases p38562_3 (m.d 0 2) (by simp) with h38582 | h38582
                                                · linarith only [h36830, h38582, hlam]
                                                · linarith only [h38457, h38582, hlam]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                rcases p38562_3 (m.d 0 2) (by simp) with h38585 | h38585
                                                · linarith only [h36830, h38585, hlam]
                                                · linarith only [h38458, h38585, hlam]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h38457, hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h38486, hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h38492, hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h38494, hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h38458, hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h38487, hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h38493, hlam, p38562_0]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [h36829, h38487, h38492, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38498_1, p38562_1]
                                              · have p38562_0 := h38562c.1
                                                have p38562_1 := h38562c.2.1
                                                have p38562_2 := h38562c.2.2.1
                                                have p38562_3 := h38562c.2.2.2
                                                linarith only [hlam, p38562_0]
                                            · rcases h2bigk with h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c | h38598c
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h0, hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h36830, hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h36830, h38485, h38492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38598_1]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h36830, h38485, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p38598_1]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                rcases p38598_3 (m.d 0 2) (by simp) with h38604 | h38604
                                                · linarith only [h0, h38604, hlam]
                                                · rcases p38598_3 (m.d 1 2) (by simp) with h38606 | h38606
                                                  · rcases p38598_3 (m.d 2 3) (by simp) with h38607 | h38607
                                                    · linarith only [h38485, h38607, hlam]
                                                    · linarith only [h36830, h38607, hlam]
                                                  · linarith only [h0, h38606, hlam]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h0, h36830, hc01, hc12, hlam, hphi, p38598_1]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h36828, h38485, h38486, hlam, p38498_1, p38598_2]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h36830, h38458, h38485, hlam, p38598_2]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h38458, h38485, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p38598_1]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h38485, hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                rcases p38598_3 (m.d 0 2) (by simp) with h38618 | h38618
                                                · linarith only [h36830, h38618, hlam]
                                                · linarith only [h38457, h38618, hlam]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                rcases p38598_3 (m.d 0 2) (by simp) with h38621 | h38621
                                                · linarith only [h36830, h38621, hlam]
                                                · linarith only [h38458, h38621, hlam]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h38457, hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h38486, hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h38492, hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h38494, hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h38458, hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h38487, hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h38493, hlam, p38598_0]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [h36830, h38458, h38485, h38492, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38598_1]
                                              · have p38598_0 := h38598c.1
                                                have p38598_1 := h38598c.2.1
                                                have p38598_2 := h38598c.2.2.1
                                                have p38598_3 := h38598c.2.2.2
                                                linarith only [hlam, p38598_0]
                                      · linarith only [h38518, hlam, p38498_0]
                                    · linarith only [h0, h38517, hlam]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h38485, hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  rcases p38498_3 (m.d 0 1) (by simp) with h38638 | h38638
                                  · linarith only [h33187, h38638, hlam]
                                  · linarith only [h36828, h38638, hlam]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  rcases p38498_3 (m.d 0 1) (by simp) with h38641 | h38641
                                  · linarith only [h33187, h38641, hlam]
                                  · linarith only [h36829, h38641, hlam]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h36828, hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h38486, hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h38488, hlam, p38498_1]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h38490, hlam, p38498_1]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h36829, hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h38487, hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h38489, hlam, p38498_0]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [h0, h36829, h36830, h38485, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p38498_1]
                                · have p38498_0 := h38498c.1
                                  have p38498_1 := h38498c.2.1
                                  have p38498_2 := h38498c.2.2.1
                                  have p38498_3 := h38498c.2.2.2
                                  linarith only [hlam, p38498_0]
                          · linarith only [h36830, h38460, h38493, hlam]
                        · linarith only [h36830, h38459, h38492, hlam]
                    · linarith only [h33187, h36828, h38460, h38486, h38489, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h36828, h36830, h38459, h38485, h38486, h38488, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h36828, h36830, h38485, h38486, h38487, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h36830, h38485, h38486, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h38660 | h38660
              · rcases m.htr 1 2 5 (by decide) (by decide) with h38661 | h38661
                · rcases m.htr 1 3 4 (by decide) (by decide) with h38662 | h38662
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h38663 | h38663
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h38664 | h38664
                      · linarith only [h0, h36828, h38485, h38664, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h38666 | h38666
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h38667 | h38667
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h38668 | h38668
                            · linarith only [h36828, h38461, h38660, h38668, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h38670 | h38670
                              · linarith only [h36828, h38461, h38660, h38666, h38670, hlam]
                              · rcases h1bigk with h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c | h38672c
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [hlam, p38672_0]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h0, hlam, p38672_0]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h33187, hlam, p38672_0]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h0, h38485, h38660, h38666, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38672_1]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h0, h38485, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p38672_1]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h38485, hc01, hc23, hlam, hphi, ht12, p38672_1]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [hlam, p38672_0]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h38485, hlam, p38672_1]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  rcases p38672_3 (m.d 0 1) (by simp) with h38681 | h38681
                                  · linarith only [h0, h38681, hlam]
                                  · linarith only [h36828, h38681, hlam]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  rcases p38672_3 (m.d 0 1) (by simp) with h38684 | h38684
                                  · linarith only [h0, h38684, hlam]
                                  · linarith only [h36829, h38684, hlam]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  rcases p38672_3 (m.d 0 1) (by simp) with h38687 | h38687
                                  · linarith only [h38687, hlam, p38672_0]
                                  · rcases p38672_3 (m.d 1 2) (by simp) with h38689 | h38689
                                    · linarith only [h38485, h38689, hlam]
                                    · linarith only [h0, h38689, hlam]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h0, h36829, h38485, h38660, h38664, h38666, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p38672_1]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [hlam, p38672_0]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  rcases p38672_3 (m.d 0 1) (by simp) with h38694 | h38694
                                  · linarith only [h33187, h38694, hlam]
                                  · linarith only [h36828, h38694, hlam]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  rcases p38672_3 (m.d 0 1) (by simp) with h38697 | h38697
                                  · linarith only [h33187, h38697, hlam]
                                  · linarith only [h36829, h38697, hlam]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h36828, hlam, p38672_0]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h38660, hlam, p38672_0]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h38662, hlam, p38672_1]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [hlam, p38672_0]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h38664, hlam, p38672_1]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h36829, hlam, p38672_0]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h38661, hlam, p38672_0]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h38663, hlam, p38672_0]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [h0, h36829, h38660, h38666, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38672_1]
                                · have p38672_0 := h38672c.1
                                  have p38672_1 := h38672c.2.1
                                  have p38672_2 := h38672c.2.2.1
                                  have p38672_3 := h38672c.2.2.2
                                  linarith only [hlam, p38672_0]
                          · linarith only [h0, h38485, h38667, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h36829, h38485, h38660, h38664, h38666, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h33187, h38460, h38663, hlam]
                  · linarith only [h33187, h38459, h38662, hlam]
                · linarith only [h0, h33187, h36830, h38458, h38661, hc01, hc13, hlam, hphi]
              · linarith only [h0, h38457, h38660, hlam]
        · linarith only [h0, h36829, h36830, h38460, hlam]
      · linarith only [h0, h36828, h36830, h38459, hlam]
    · linarith only [h0, h36829, h38458, hlam]
  · linarith only [h0, h36828, h38457, hlam]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  rcases m.htr 0 2 3 (by decide) (by decide) with h36830 | h36830
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 h36828 h36829 h36830
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 h36828 h36829 h36830

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h36829 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  rcases m.htr 0 2 3 (by decide) (by decide) with h38720 | h38720
  · rcases m.htr 0 2 4 (by decide) (by decide) with h38721 | h38721
    · rcases m.htr 0 2 5 (by decide) (by decide) with h38722 | h38722
      · rcases m.htr 0 3 4 (by decide) (by decide) with h38723 | h38723
        · rcases m.htr 0 3 5 (by decide) (by decide) with h38724 | h38724
          · rcases m.htr 0 4 5 (by decide) (by decide) with h38725 | h38725
            · linarith only [h36828, h36829, h38725, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h38727 | h38727
              · rcases m.htr 1 2 4 (by decide) (by decide) with h38728 | h38728
                · rcases m.htr 1 2 5 (by decide) (by decide) with h38729 | h38729
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h38730 | h38730
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h38731 | h38731
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h38732 | h38732
                        · linarith only [h36828, h36829, h38725, h38727, h38731, h38732, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h38734 | h38734
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h38735 | h38735
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h38736 | h38736
                              · linarith only [h36828, h36829, h38728, h38732, h38736, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h38738 | h38738
                                · linarith only [h36829, h38720, h38732, h38734, h38738, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases h1bigk with h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c | h38740c
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h0, hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h33187, hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h36829, h38728, h38732, h38734, hc34, hc45, hlam, hphi, p38740_1]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h36829, hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    rcases p38740_3 (m.d 0 1) (by simp) with h38746 | h38746
                                    · linarith only [h38746, hlam, p38740_0]
                                    · rcases p38740_3 (m.d 1 2) (by simp) with h38748 | h38748
                                      · rcases p38740_3 (m.d 1 3) (by simp) with h38749 | h38749
                                        · linarith only [h38727, h38749, hlam]
                                        · linarith only [h33187, h38749, hlam]
                                      · linarith only [h38748, hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h33187, hc01, hc12, hlam, hphi, p38740_1]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    rcases p38740_3 (m.d 0 1) (by simp) with h38755 | h38755
                                    · linarith only [h0, h38755, hlam]
                                    · linarith only [h36828, h38755, hlam]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h36828, h36829, h38728, h38734, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38740_1]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    rcases p38740_3 (m.d 0 1) (by simp) with h38759 | h38759
                                    · linarith only [h38759, hlam, p38740_0]
                                    · rcases p38740_3 (m.d 1 2) (by simp) with h38761 | h38761
                                      · rcases p38740_3 (m.d 1 3) (by simp) with h38762 | h38762
                                        · rcases p38740_3 (m.d 1 4) (by simp) with h38763 | h38763
                                          · linarith only [h38730, h38763, hlam]
                                          · rcases p38740_3 (m.d 1 5) (by simp) with h38765 | h38765
                                            · linarith only [h38731, h38765, hlam]
                                            · linarith only [h36829, h38765, hlam]
                                        · linarith only [h38762, hlam, p38740_0]
                                      · linarith only [h0, h38761, hlam]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h38727, hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    rcases p38740_3 (m.d 0 1) (by simp) with h38772 | h38772
                                    · linarith only [h33187, h38772, hlam]
                                    · linarith only [h36828, h38772, hlam]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h36828, h36829, h38728, h38734, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38740_1]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h36828, hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h38728, hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h38730, hlam, p38740_1]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h38732, hlam, p38740_1]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h36828, h38728, h38732, h38734, hc34, hc45, hlam, hphi, p38740_1]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h38729, hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [h38731, hlam, p38740_0]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    rcases p38740_3 (m.d 0 1) (by simp) with h38784 | h38784
                                    · linarith only [h36829, h38784, hlam]
                                    · linarith only [h36828, h38784, hlam]
                                  · have p38740_0 := h38740c.1
                                    have p38740_1 := h38740c.2.1
                                    have p38740_2 := h38740c.2.2.1
                                    have p38740_3 := h38740c.2.2.2
                                    linarith only [hlam, p38740_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h38788 | h38788
                              · linarith only [h36828, h36829, h38728, h38732, h38788, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h38790 | h38790
                                · linarith only [h36829, h38724, h38732, h38734, h38735, h38790, hc01, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases h1bigk with h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c | h38792c
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h0, hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h33187, hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h36829, h38728, h38732, h38734, hc34, hc45, hlam, hphi, p38792_1]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h36829, hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    rcases p38792_3 (m.d 0 1) (by simp) with h38798 | h38798
                                    · linarith only [h38798, hlam, p38792_0]
                                    · rcases p38792_3 (m.d 1 2) (by simp) with h38800 | h38800
                                      · rcases p38792_3 (m.d 1 3) (by simp) with h38801 | h38801
                                        · linarith only [h38727, h38801, hlam]
                                        · linarith only [h33187, h38801, hlam]
                                      · linarith only [h38800, hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h33187, hc01, hc12, hlam, hphi, p38792_1]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    rcases p38792_3 (m.d 0 1) (by simp) with h38807 | h38807
                                    · linarith only [h0, h38807, hlam]
                                    · linarith only [h36828, h38807, hlam]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h36829, hc01, hc12, hlam, hphi, p38792_1]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    rcases p38792_3 (m.d 0 1) (by simp) with h38811 | h38811
                                    · linarith only [h38811, hlam, p38792_0]
                                    · rcases p38792_3 (m.d 1 2) (by simp) with h38813 | h38813
                                      · rcases p38792_3 (m.d 1 3) (by simp) with h38814 | h38814
                                        · rcases p38792_3 (m.d 1 4) (by simp) with h38815 | h38815
                                          · linarith only [h38730, h38815, hlam]
                                          · rcases p38792_3 (m.d 1 5) (by simp) with h38817 | h38817
                                            · linarith only [h38731, h38817, hlam]
                                            · linarith only [h36829, h38817, hlam]
                                        · linarith only [h38814, hlam, p38792_0]
                                      · linarith only [h0, h38813, hlam]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h38727, hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    rcases p38792_3 (m.d 0 1) (by simp) with h38824 | h38824
                                    · linarith only [h33187, h38824, hlam]
                                    · linarith only [h36828, h38824, hlam]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h36829, h38724, h38727, h38734, h38735, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38792_1]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h36828, hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h38728, hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h38730, hlam, p38792_1]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h38732, hlam, p38792_1]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h36828, h38728, h38732, h38734, hc34, hc45, hlam, hphi, p38792_1]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h38729, hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [h38731, hlam, p38792_0]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    rcases p38792_3 (m.d 0 1) (by simp) with h38836 | h38836
                                    · linarith only [h36829, h38836, hlam]
                                    · linarith only [h36828, h38836, hlam]
                                  · have p38792_0 := h38792c.1
                                    have p38792_1 := h38792c.2.1
                                    have p38792_2 := h38792c.2.2.1
                                    have p38792_3 := h38792c.2.2.2
                                    linarith only [hlam, p38792_0]
                          · linarith only [h36828, h36829, h38730, h38732, h38734, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h33187, h38720, h38724, h38731, hc01, hc12, hlam, hphi]
                    · linarith only [h33187, h38723, h38730, hlam]
                  · linarith only [h0, h38720, h38722, h38724, h38729, hlam]
                · linarith only [h0, h38721, h38728, hlam]
              · linarith only [h0, h38720, h38727, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h38846 | h38846
            · linarith only [h33187, h36828, h38724, h38846, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h38848 | h38848
              · rcases m.htr 1 2 4 (by decide) (by decide) with h38849 | h38849
                · rcases m.htr 1 2 5 (by decide) (by decide) with h38850 | h38850
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h38851 | h38851
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h38852 | h38852
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h38853 | h38853
                        · linarith only [h33187, h36828, h38724, h38846, h38848, h38852, h38853, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h38855 | h38855
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h38856 | h38856
                            · linarith only [h38720, h38724, h38856, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h38858 | h38858
                              · linarith only [h33187, h36828, h38724, h38849, h38852, h38853, h38858, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h38860 | h38860
                                · linarith only [h38723, h38724, h38852, h38853, h38860, hlam]
                                · rcases h1bigk with h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c | h38862c
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h0, hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h33187, hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h33187, h38724, h38848, h38852, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p38862_1]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h36829, hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    rcases p38862_3 (m.d 0 1) (by simp) with h38868 | h38868
                                    · linarith only [h38868, hlam, p38862_0]
                                    · rcases p38862_3 (m.d 1 2) (by simp) with h38870 | h38870
                                      · rcases p38862_3 (m.d 1 3) (by simp) with h38871 | h38871
                                        · linarith only [h38848, h38871, hlam]
                                        · linarith only [h33187, h38871, hlam]
                                      · linarith only [h38870, hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h33187, h38724, h38852, hc01, hc12, hlam, hphi, p38862_1]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h33187, h36828, h38724, h38848, h38852, hlam, p38862_2]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h33187, h36828, h38724, h38849, h38852, h38855, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38862_1]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    rcases p38862_3 (m.d 0 1) (by simp) with h38879 | h38879
                                    · linarith only [h38879, hlam, p38862_0]
                                    · rcases p38862_3 (m.d 1 2) (by simp) with h38881 | h38881
                                      · rcases p38862_3 (m.d 1 3) (by simp) with h38882 | h38882
                                        · rcases p38862_3 (m.d 1 4) (by simp) with h38883 | h38883
                                          · linarith only [h38851, h38883, hlam]
                                          · rcases p38862_3 (m.d 1 5) (by simp) with h38885 | h38885
                                            · linarith only [h38852, h38885, hlam]
                                            · linarith only [h36829, h38885, hlam]
                                        · linarith only [h38882, hlam, p38862_0]
                                      · linarith only [h0, h38881, hlam]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h38848, hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h33187, h36828, h38724, h38852, hlam, p38862_2]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h33187, h36828, h38724, h38849, h38852, h38855, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38862_1]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h36828, hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h38849, hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h38851, hlam, p38862_1]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h38853, hlam, p38862_1]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h36828, h38849, h38853, h38855, hc34, hc45, hlam, hphi, p38862_1]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h38850, hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [h38852, hlam, p38862_0]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    rcases p38862_3 (m.d 0 1) (by simp) with h38902 | h38902
                                    · linarith only [h36829, h38902, hlam]
                                    · linarith only [h36828, h38902, hlam]
                                  · have p38862_0 := h38862c.1
                                    have p38862_1 := h38862c.2.1
                                    have p38862_2 := h38862c.2.2.1
                                    have p38862_3 := h38862c.2.2.2
                                    linarith only [hlam, p38862_0]
                          · linarith only [h38723, h38724, h38855, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h38907 | h38907
                        · linarith only [h33187, h36828, h38852, h38907, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h38909 | h38909
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h38910 | h38910
                            · linarith only [h33187, h38852, h38910, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h38912 | h38912
                              · linarith only [h33187, h36828, h38849, h38852, h38907, h38912, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h38914 | h38914
                                · linarith only [h33187, h36828, h38849, h38852, h38907, h38909, h38914, hlam]
                                · linarith only [h33187, h36828, h38849, h38852, h38909, h38914, hc34, hc45, hlam, hphi]
                          · linarith only [h33187, h38723, h38852, h38909, hc23, hc35, hlam, hphi]
                    · linarith only [h33187, h36828, h38723, h38851, hlam]
                  · linarith only [h0, h38722, h38850, hlam]
                · linarith only [h0, h38721, h38849, hlam]
              · linarith only [h0, h38720, h38848, hlam]
        · linarith only [h33187, h36828, h38723, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h38923 | h38923
        · rcases m.htr 0 3 5 (by decide) (by decide) with h38924 | h38924
          · linarith only [h38720, h38722, h38924, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h38926 | h38926
            · linarith only [h0, h36828, h38722, h38926, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h38928 | h38928
              · rcases m.htr 1 2 4 (by decide) (by decide) with h38929 | h38929
                · rcases m.htr 1 2 5 (by decide) (by decide) with h38930 | h38930
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h38931 | h38931
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h38932 | h38932
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h38933 | h38933
                        · linarith only [h33187, h36828, h38720, h38722, h38926, h38930, h38933, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h38935 | h38935
                          · linarith only [h38720, h38722, h38930, h38935, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h38720, h38722, h38923, h38930, h38935, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h38938 | h38938
                        · linarith only [h33187, h36828, h38720, h38722, h38930, h38938, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h38940 | h38940
                          · linarith only [h38720, h38722, h38930, h38940, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h38720, h38722, h38923, h38930, h38940, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h33187, h36828, h38923, h38931, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h38944 | h38944
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h38945 | h38945
                      · linarith only [h33187, h38924, h38928, h38930, h38945, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h38947 | h38947
                        · linarith only [h0, h36828, h38930, h38947, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h38949 | h38949
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h38950 | h38950
                            · linarith only [h33187, h36828, h38929, h38945, h38949, h38950, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h38952 | h38952
                              · linarith only [h33187, h36828, h38928, h38929, h38930, h38947, h38950, h38952, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h33187, h36828, h38928, h38929, h38930, h38949, h38952, hc34, hc45, hlam, hphi]
                          · linarith only [h38923, h38924, h38949, hc23, hc35, hlam, hphi]
                    · linarith only [h33187, h36828, h38923, h38944, hlam]
                · linarith only [h0, h38721, h38929, hlam]
              · linarith only [h0, h38720, h38928, hlam]
        · linarith only [h33187, h36828, h38923, hlam]
    · linarith only [h0, h36828, h38721, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h38961 | h38961
    · rcases m.htr 0 2 5 (by decide) (by decide) with h38962 | h38962
      · rcases m.htr 0 3 4 (by decide) (by decide) with h38963 | h38963
        · rcases m.htr 0 3 5 (by decide) (by decide) with h38964 | h38964
          · rcases m.htr 0 4 5 (by decide) (by decide) with h38965 | h38965
            · linarith only [h36828, h36829, h38965, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h38967 | h38967
              · rcases m.htr 1 2 4 (by decide) (by decide) with h38968 | h38968
                · rcases m.htr 1 2 5 (by decide) (by decide) with h38969 | h38969
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h38970 | h38970
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h38971 | h38971
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h38972 | h38972
                        · linarith only [h36828, h36829, h38720, h38962, h38965, h38967, h38972, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h38974 | h38974
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h38975 | h38975
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h38976 | h38976
                              · linarith only [h36828, h36829, h38968, h38972, h38976, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h38978 | h38978
                                · linarith only [h36828, h36829, h38968, h38972, h38974, h38978, hlam]
                                · rcases h1bigk with h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c | h38980c
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h0, hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h33187, hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h36829, h38720, h38962, h38967, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p38980_1]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h36829, hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    rcases p38980_3 (m.d 0 1) (by simp) with h38986 | h38986
                                    · linarith only [h38986, hlam, p38980_0]
                                    · rcases p38980_3 (m.d 1 2) (by simp) with h38988 | h38988
                                      · rcases p38980_3 (m.d 1 3) (by simp) with h38989 | h38989
                                        · linarith only [h38967, h38989, hlam]
                                        · linarith only [h33187, h38989, hlam]
                                      · linarith only [h38988, hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h36829, h38720, h38962, h38967, hc01, hc12, hlam, hphi, p38980_1]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h36828, h36829, h38720, h38962, h38967, hlam, p38980_2]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h36828, h36829, h38968, h38974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38980_1]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    rcases p38980_3 (m.d 0 1) (by simp) with h38997 | h38997
                                    · linarith only [h38997, hlam, p38980_0]
                                    · rcases p38980_3 (m.d 1 2) (by simp) with h38999 | h38999
                                      · rcases p38980_3 (m.d 1 3) (by simp) with h39000 | h39000
                                        · rcases p38980_3 (m.d 1 4) (by simp) with h39001 | h39001
                                          · linarith only [h38970, h39001, hlam]
                                          · rcases p38980_3 (m.d 1 5) (by simp) with h39003 | h39003
                                            · linarith only [h38971, h39003, hlam]
                                            · linarith only [h36829, h39003, hlam]
                                        · linarith only [h39000, hlam, p38980_0]
                                      · linarith only [h0, h38999, hlam]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h38967, hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    rcases p38980_3 (m.d 0 1) (by simp) with h39010 | h39010
                                    · linarith only [h33187, h39010, hlam]
                                    · linarith only [h36828, h39010, hlam]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h36828, h36829, h38968, h38974, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p38980_1]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h36828, hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h38968, hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h38970, hlam, p38980_1]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h38972, hlam, p38980_1]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h36828, h38968, h38972, h38974, hc34, hc45, hlam, hphi, p38980_1]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h38969, hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [h38971, hlam, p38980_0]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    rcases p38980_3 (m.d 0 1) (by simp) with h39022 | h39022
                                    · linarith only [h36829, h39022, hlam]
                                    · linarith only [h36828, h39022, hlam]
                                  · have p38980_0 := h38980c.1
                                    have p38980_1 := h38980c.2.1
                                    have p38980_2 := h38980c.2.2.1
                                    have p38980_3 := h38980c.2.2.2
                                    linarith only [hlam, p38980_0]
                            · linarith only [h36828, h36829, h38720, h38962, h38964, h38968, h38974, h38975, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h36828, h36829, h38720, h38962, h38963, h38968, h38974, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h33187, h36828, h38964, h38968, h38971, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h33187, h38963, h38970, hlam]
                  · linarith only [h36828, h36829, h38720, h38962, h38967, h38968, h38969, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h36828, h36829, h38720, h38962, h38967, h38968, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h39032 | h39032
                · rcases m.htr 1 2 5 (by decide) (by decide) with h39033 | h39033
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h39034 | h39034
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h39035 | h39035
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h39036 | h39036
                        · linarith only [h36828, h38965, h39036, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39038 | h39038
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h39039 | h39039
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h39040 | h39040
                              · linarith only [h36828, h36829, h39032, h39036, h39040, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h39042 | h39042
                                · linarith only [h36828, h36829, h38963, h39032, h39036, h39042, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases h1bigk with h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c | h39044c
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [hlam, p39044_0]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h0, hlam, p39044_0]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h33187, hlam, p39044_0]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h36829, h38967, h39033, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p39044_1]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h36829, hlam, p39044_0]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h38967, hc01, hc23, hlam, hphi, ht12, p39044_1]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [hlam, p39044_0]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h38967, hlam, p39044_1]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    rcases p39044_3 (m.d 0 1) (by simp) with h39053 | h39053
                                    · linarith only [h0, h39053, hlam]
                                    · linarith only [h36828, h39053, hlam]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h36828, h36829, h38967, h39032, h39038, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p39044_1]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    rcases p39044_3 (m.d 0 1) (by simp) with h39057 | h39057
                                    · linarith only [h39057, hlam, p39044_0]
                                    · rcases p39044_3 (m.d 1 2) (by simp) with h39059 | h39059
                                      · linarith only [h38967, h39059, hlam]
                                      · linarith only [h0, h39059, hlam]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h0, h36828, h39032, h39038, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39044_1]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [hlam, p39044_0]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    rcases p39044_3 (m.d 0 1) (by simp) with h39064 | h39064
                                    · linarith only [h33187, h39064, hlam]
                                    · linarith only [h36828, h39064, hlam]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h36828, h36829, h39032, h39038, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39044_1]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h36828, hlam, p39044_0]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h39032, hlam, p39044_0]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h39034, hlam, p39044_1]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [hlam, p39044_0]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h39036, hlam, p39044_1]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h36828, h39032, h39036, h39038, hc34, hc45, hlam, hphi, p39044_1]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h39033, hlam, p39044_0]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [h39035, hlam, p39044_0]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    rcases p39044_3 (m.d 0 1) (by simp) with h39076 | h39076
                                    · linarith only [h36829, h39076, hlam]
                                    · linarith only [h36828, h39076, hlam]
                                  · have p39044_0 := h39044c.1
                                    have p39044_1 := h39044c.2.1
                                    have p39044_2 := h39044c.2.2.1
                                    have p39044_3 := h39044c.2.2.2
                                    linarith only [hlam, p39044_0]
                            · linarith only [h0, h36828, h38967, h39032, h39038, h39039, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h36828, h36829, h38967, h39032, h39033, h39038, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h33187, h36828, h38962, h38964, h38967, h39032, h39035, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h33187, h38963, h39034, hlam]
                  · linarith only [h0, h38962, h39033, hlam]
                · linarith only [h0, h38961, h39032, hlam]
          · linarith only [h38720, h38962, h38964, hlam]
        · linarith only [h0, h36828, h38720, h38963, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h39088 | h39088
        · rcases m.htr 0 3 5 (by decide) (by decide) with h39089 | h39089
          · rcases m.htr 0 4 5 (by decide) (by decide) with h39090 | h39090
            · linarith only [h0, h36828, h38962, h39090, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h39092 | h39092
              · rcases m.htr 1 2 4 (by decide) (by decide) with h39093 | h39093
                · rcases m.htr 1 2 5 (by decide) (by decide) with h39094 | h39094
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h39095 | h39095
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h39096 | h39096
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h39097 | h39097
                        · linarith only [h0, h36828, h38720, h39090, h39092, h39097, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39099 | h39099
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h39100 | h39100
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h39101 | h39101
                              · linarith only [h0, h36828, h38962, h39093, h39094, h39097, h39101, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h39103 | h39103
                                · linarith only [h0, h36828, h38962, h39093, h39094, h39097, h39099, h39103, hlam]
                                · rcases h1bigk with h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c | h39105c
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h0, hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h33187, hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h0, h38962, h39092, h39100, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p39105_1]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h36829, hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    rcases p39105_3 (m.d 0 1) (by simp) with h39111 | h39111
                                    · linarith only [h39111, hlam, p39105_0]
                                    · rcases p39105_3 (m.d 1 2) (by simp) with h39113 | h39113
                                      · rcases p39105_3 (m.d 1 3) (by simp) with h39114 | h39114
                                        · linarith only [h39092, h39114, hlam]
                                        · linarith only [h33187, h39114, hlam]
                                      · linarith only [h39113, hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h0, h38962, h39094, h39096, hc01, hc12, hlam, hphi, p39105_1]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h0, h36828, h38720, h39092, hlam, p39105_2]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h0, h36828, h38962, h39093, h39094, h39099, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39105_1]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    rcases p39105_3 (m.d 0 1) (by simp) with h39122 | h39122
                                    · linarith only [h39122, hlam, p39105_0]
                                    · rcases p39105_3 (m.d 1 2) (by simp) with h39124 | h39124
                                      · rcases p39105_3 (m.d 1 3) (by simp) with h39125 | h39125
                                        · rcases p39105_3 (m.d 1 4) (by simp) with h39126 | h39126
                                          · linarith only [h39095, h39126, hlam]
                                          · rcases p39105_3 (m.d 1 5) (by simp) with h39128 | h39128
                                            · linarith only [h39096, h39128, hlam]
                                            · linarith only [h36829, h39128, hlam]
                                        · linarith only [h39125, hlam, p39105_0]
                                      · linarith only [h0, h39124, hlam]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h39092, hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    rcases p39105_3 (m.d 0 1) (by simp) with h39135 | h39135
                                    · linarith only [h33187, h39135, hlam]
                                    · linarith only [h36828, h39135, hlam]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h0, h36828, h38962, h39093, h39094, h39099, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p39105_1]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h36828, hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h39093, hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h39095, hlam, p39105_1]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h39097, hlam, p39105_1]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h36828, h39093, h39097, h39099, hc34, hc45, hlam, hphi, p39105_1]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h39094, hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [h39096, hlam, p39105_0]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    rcases p39105_3 (m.d 0 1) (by simp) with h39147 | h39147
                                    · linarith only [h36829, h39147, hlam]
                                    · linarith only [h36828, h39147, hlam]
                                  · have p39105_0 := h39105c.1
                                    have p39105_1 := h39105c.2.1
                                    have p39105_2 := h39105c.2.2.1
                                    have p39105_3 := h39105c.2.2.2
                                    linarith only [hlam, p39105_0]
                            · linarith only [h0, h36828, h38720, h39089, h39093, h39099, h39100, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h36828, h38720, h39088, h39093, h39099, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h33187, h36828, h39089, h39093, h39096, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h33187, h39088, h39095, hlam]
                  · linarith only [h0, h36828, h38720, h39092, h39093, h39094, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h36828, h38720, h39092, h39093, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h39157 | h39157
                · rcases m.htr 1 2 5 (by decide) (by decide) with h39158 | h39158
                  · linarith only [h0, h36828, h38962, h39092, h39157, h39158, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h39160 | h39160
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h39161 | h39161
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h39162 | h39162
                        · linarith only [h0, h36828, h39092, h39162, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39164 | h39164
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h39165 | h39165
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h39166 | h39166
                              · linarith only [h0, h36828, h39157, h39158, h39162, h39165, h39166, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h36828, h39157, h39158, h39164, h39166, hc34, hc45, hlam, hphi]
                            · linarith only [h33187, h39089, h39092, h39165, hlam]
                          · linarith only [h0, h39092, h39164, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h33187, h39089, h39161, hlam]
                    · linarith only [h33187, h39088, h39160, hlam]
                · linarith only [h0, h36828, h38961, h39157, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h39174 | h39174
            · linarith only [h33187, h36828, h39089, h39174, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h39176 | h39176
              · rcases m.htr 1 2 4 (by decide) (by decide) with h39177 | h39177
                · rcases m.htr 1 2 5 (by decide) (by decide) with h39178 | h39178
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h39179 | h39179
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h39180 | h39180
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h39181 | h39181
                        · linarith only [h0, h36828, h38720, h39089, h39174, h39180, h39181, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39183 | h39183
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h39184 | h39184
                            · linarith only [h0, h38720, h39089, h39176, h39184, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h36828, h38720, h39176, h39177, h39180, h39183, h39184, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h36828, h38720, h39088, h39089, h39183, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h39188 | h39188
                        · linarith only [h33187, h36828, h39180, h39188, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39190 | h39190
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h39191 | h39191
                            · linarith only [h39176, h39180, h39191, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h39193 | h39193
                              · linarith only [h0, h36828, h38720, h38962, h39176, h39177, h39178, h39180, h39188, h39193, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h39195 | h39195
                                · linarith only [h0, h36828, h38720, h39176, h39177, h39180, h39188, h39190, h39195, hlam]
                                · linarith only [h0, h36828, h38720, h39176, h39180, h39195, hc14, hc45, hlam, hphi]
                          · linarith only [h0, h36828, h38720, h39088, h39177, h39190, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h33187, h36828, h39088, h39179, hlam]
                  · linarith only [h0, h36828, h38720, h39176, h39177, h39178, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h36828, h38720, h39176, h39177, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h39202 | h39202
                · rcases m.htr 1 2 5 (by decide) (by decide) with h39203 | h39203
                  · linarith only [h0, h36828, h38962, h39176, h39202, h39203, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h39205 | h39205
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h39206 | h39206
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h39207 | h39207
                        · linarith only [h0, h36828, h39176, h39207, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39209 | h39209
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h39210 | h39210
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h39211 | h39211
                              · linarith only [h0, h36828, h38720, h39089, h39176, h39202, h39203, h39206, h39207, h39211, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h36828, h39202, h39203, h39209, h39211, hc34, hc45, hlam, hphi]
                            · linarith only [h39176, h39206, h39210, hlam]
                          · linarith only [h0, h36828, h38720, h39089, h39176, h39202, h39206, h39209, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h39216 | h39216
                        · linarith only [h0, h36828, h39176, h39206, h39216, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h39218 | h39218
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h39219 | h39219
                            · linarith only [h0, h36828, h39176, h39202, h39206, h39218, h39219, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h36828, h39176, h39202, h39218, h39219, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h36828, h39176, h39202, h39218, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h36828, h39088, h39176, h39202, h39205, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h38961, h39202, hlam]
        · linarith only [h33187, h36828, h39088, hlam]
    · linarith only [h0, h36828, h38961, hlam]

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  rcases m.htr 0 1 5 (by decide) (by decide) with h36829 | h36829
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 h36828 h36829
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 h36828 h36829

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38 m hb1 hb2 hb4 hb5 h0 h33187 h36828

set_option maxHeartbeats 22102000 in
set_option maxHeartbeats 22102000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  rcases m.htr 0 1 4 (by decide) (by decide) with h36828 | h36828
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 h36828
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 h36828

set_option maxHeartbeats 29384000 in
set_option maxHeartbeats 29384000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s30 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h33187 | h33187
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s31 m hb1 hb2 hb4 hb5 h0 h33187
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s37 m hb1 hb2 hb4 hb5 h0 h33187

set_option maxHeartbeats 95758000 in
set_option maxHeartbeats 95758000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s30 m hb1 hb2 hb4 hb5 h0

end R2N4
