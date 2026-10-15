import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_40S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 5 (by decide) (by decide) with h559 | h559
  · rcases m.htr 1 3 4 (by decide) (by decide) with h560 | h560
    · rcases m.htr 1 3 5 (by decide) (by decide) with h561 | h561
      · rcases m.htr 1 4 5 (by decide) (by decide) with h562 | h562
        · rcases m.htr 2 3 4 (by decide) (by decide) with h563 | h563
          · rcases m.htr 2 3 5 (by decide) (by decide) with h564 | h564
            · rcases m.htr 2 4 5 (by decide) (by decide) with h565 | h565
              · rcases m.htr 3 4 5 (by decide) (by decide) with h566 | h566
                · rcases h3bigk with h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c | h567c
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h0, h4, h560, h566, hc01, hc45, hlam, hphi, ht0b, ht5b, p567_1]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h0, h4, h559, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p567_1]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    rcases p567_3 (m.d 0 3) (by simp) with h571 | h571
                    · rcases p567_3 (m.d 1 3) (by simp) with h572 | h572
                      · linarith only [h1, h572, hlam]
                      · linarith only [h560, h572, hlam]
                    · linarith only [h571, hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    rcases p567_3 (m.d 0 3) (by simp) with h576 | h576
                    · rcases p567_3 (m.d 1 3) (by simp) with h577 | h577
                      · linarith only [h1, h577, hlam]
                      · linarith only [h561, h577, hlam]
                    · linarith only [h576, hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h1, hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h9, hlam, p567_1]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h1, h566, hc01, hc45, hlam, hphi, ht0b, ht5b, p567_1]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    rcases p567_3 (m.d 0 3) (by simp) with h585 | h585
                    · rcases p567_3 (m.d 1 3) (by simp) with h586 | h586
                      · rcases p567_3 (m.d 2 3) (by simp) with h587 | h587
                        · rcases p567_3 (m.d 3 4) (by simp) with h588 | h588
                          · linarith only [h560, h588, hlam]
                          · linarith only [h566, h588, hlam]
                        · linarith only [h564, h587, hlam]
                      · linarith only [h586, hlam, p567_0]
                    · linarith only [h585, h7, hlam]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h4, hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p567_1, u1ehi2]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h0, h4, h566, hc01, hc45, hlam, hphi, ht0b, ht5b, p567_1]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    rcases p567_3 (m.d 0 3) (by simp) with h598 | h598
                    · rcases p567_3 (m.d 1 3) (by simp) with h599 | h599
                      · linarith only [h599, h9, hlam]
                      · linarith only [h561, h599, hlam]
                    · linarith only [h598, h7, hlam]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h6, hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h560, hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h563, hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h1, h560, h566, hc01, hc45, hlam, hphi, ht0b, ht5b, p567_1]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h7, hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h561, hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h564, hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [h566, hlam, p567_0]
                  · have p567_0 := h567c.1
                    have p567_1 := h567c.2.1
                    have p567_2 := h567c.2.2.1
                    have p567_3 := h567c.2.2.2
                    linarith only [hlam, p567_0]
                · linarith only [h0, h4, h559, h565, h566, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h614 | h614
                · linarith only [h563, h565, h614, hlam]
                · rcases h3bigk with h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c | h616c
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h0, h4, h560, h562, h563, h565, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p616_1]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h0, h4, h559, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p616_1]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    rcases p616_3 (m.d 0 3) (by simp) with h620 | h620
                    · rcases p616_3 (m.d 1 3) (by simp) with h621 | h621
                      · linarith only [h1, h621, hlam]
                      · linarith only [h560, h621, hlam]
                    · linarith only [h620, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    rcases p616_3 (m.d 0 3) (by simp) with h625 | h625
                    · rcases p616_3 (m.d 1 3) (by simp) with h626 | h626
                      · linarith only [h1, h626, hlam]
                      · linarith only [h561, h626, hlam]
                    · linarith only [h625, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h1, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h9, hlam, p616_1]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    rcases p616_3 (m.d 0 3) (by simp) with h633 | h633
                    · rcases p616_3 (m.d 1 3) (by simp) with h634 | h634
                      · rcases p616_3 (m.d 2 3) (by simp) with h635 | h635
                        · rcases p616_3 (m.d 3 4) (by simp) with h636 | h636
                          · linarith only [h636, hlam, p616_0]
                          · rcases p616_3 (m.d 3 5) (by simp) with h638 | h638
                            · linarith only [h561, h638, hlam]
                            · linarith only [h614, h638, hlam]
                        · linarith only [h563, h635, hlam]
                      · linarith only [h634, hlam, p616_0]
                    · linarith only [h6, h633, hlam]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    rcases p616_3 (m.d 0 3) (by simp) with h644 | h644
                    · rcases p616_3 (m.d 1 3) (by simp) with h645 | h645
                      · rcases p616_3 (m.d 2 3) (by simp) with h646 | h646
                        · rcases p616_3 (m.d 3 4) (by simp) with h647 | h647
                          · linarith only [h560, h647, hlam]
                          · rcases p616_3 (m.d 3 5) (by simp) with h649 | h649
                            · linarith only [h649, hlam, p616_0]
                            · rcases h5bigk with h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h562, h565, h6, h8, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                rcases p651_3 (m.d 0 5) (by simp) with h654 | h654
                                · rcases p651_3 (m.d 1 5) (by simp) with h655 | h655
                                  · linarith only [h3, h655, hlam]
                                  · linarith only [h559, h655, hlam]
                                · linarith only [h5, h654, hlam]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                rcases p651_3 (m.d 0 5) (by simp) with h659 | h659
                                · rcases p651_3 (m.d 1 5) (by simp) with h660 | h660
                                  · linarith only [h3, h660, hlam]
                                  · linarith only [h561, h660, hlam]
                                · linarith only [h659, h7, hlam]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h0, h4, h563, h565, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h3, hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h559, h564, h614, h9, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h0, h4, h559, h614, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h0, h4, h559, h563, h565, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h5, hlam, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h559, hlam, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h0, h5, h614, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h565, hlam, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h7, hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h561, hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h564, hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h614, hlam, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h8, hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h562, hlam, p651_0]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h0, h4, h559, h560, h562, h9, hc01, hc13, hc25, hlam, hphi, ht0b, ht5b, p651_1, u1ehi4]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [h0, h4, h560, h562, h614, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p651_1]
                              · have p651_0 := h651c.1
                                have p651_1 := h651c.2.1
                                have p651_2 := h651c.2.2.1
                                have p651_3 := h651c.2.2.2
                                linarith only [hlam, p651_0]
                        · linarith only [h564, h646, hlam]
                      · linarith only [h645, hlam, p616_0]
                    · linarith only [h644, h7, hlam]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h4, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h0, h4, h560, h562, hc01, hc45, hlam, hphi, ht0b, ht5b, p616_1]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    rcases p616_3 (m.d 0 3) (by simp) with h691 | h691
                    · rcases p616_3 (m.d 1 3) (by simp) with h692 | h692
                      · linarith only [h692, h9, hlam]
                      · linarith only [h560, h692, hlam]
                    · linarith only [h6, h691, hlam]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    rcases p616_3 (m.d 0 3) (by simp) with h696 | h696
                    · rcases p616_3 (m.d 1 3) (by simp) with h697 | h697
                      · linarith only [h697, h9, hlam]
                      · linarith only [h561, h697, hlam]
                    · linarith only [h696, h7, hlam]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h6, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h560, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h563, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h614, hlam, p616_1]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h7, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h561, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h564, hlam, p616_0]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [h0, h4, h559, h564, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p616_1]
                  · have p616_0 := h616c.1
                    have p616_1 := h616c.2.1
                    have p616_2 := h616c.2.2.1
                    have p616_3 := h616c.2.2.2
                    linarith only [hlam, p616_0]
            · linarith only [h559, h561, h564, h9, hc13, hlam, hphi, u1ehi4]
          · linarith only [h559, h563, h9, hc34, hlam, hphi, ht12, ht23, u1ehi4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h713 | h713
          · rcases m.htr 2 3 5 (by decide) (by decide) with h714 | h714
            · rcases m.htr 2 4 5 (by decide) (by decide) with h715 | h715
              · linarith only [h562, h715, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h717 | h717
                · linarith only [h0, h4, h559, h562, h713, h715, h717, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                · rcases h3bigk with h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c | h719c
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    rcases p719_3 (m.d 0 3) (by simp) with h721 | h721
                    · rcases p719_3 (m.d 1 3) (by simp) with h722 | h722
                      · linarith only [h1, h722, hlam]
                      · rcases p719_3 (m.d 2 3) (by simp) with h724 | h724
                        · linarith only [h4, h724, hlam]
                        · linarith only [h724, h9, hlam]
                    · linarith only [h1, h721, hlam]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h0, h4, h559, h715, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p719_1]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    rcases p719_3 (m.d 0 3) (by simp) with h729 | h729
                    · rcases p719_3 (m.d 1 3) (by simp) with h730 | h730
                      · linarith only [h1, h730, hlam]
                      · linarith only [h560, h730, hlam]
                    · linarith only [h729, hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    rcases p719_3 (m.d 0 3) (by simp) with h734 | h734
                    · rcases p719_3 (m.d 1 3) (by simp) with h735 | h735
                      · linarith only [h1, h735, hlam]
                      · linarith only [h561, h735, hlam]
                    · linarith only [h734, hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h1, hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h9, hlam, p719_1]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    rcases p719_3 (m.d 0 3) (by simp) with h742 | h742
                    · rcases p719_3 (m.d 1 3) (by simp) with h743 | h743
                      · rcases p719_3 (m.d 2 3) (by simp) with h744 | h744
                        · rcases p719_3 (m.d 3 4) (by simp) with h745 | h745
                          · linarith only [h745, hlam, p719_0]
                          · rcases p719_3 (m.d 3 5) (by simp) with h747 | h747
                            · linarith only [h561, h747, hlam]
                            · linarith only [h717, h747, hlam]
                        · linarith only [h713, h744, hlam]
                      · linarith only [h743, hlam, p719_0]
                    · linarith only [h6, h742, hlam]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    rcases p719_3 (m.d 0 3) (by simp) with h753 | h753
                    · rcases p719_3 (m.d 1 3) (by simp) with h754 | h754
                      · rcases p719_3 (m.d 2 3) (by simp) with h755 | h755
                        · rcases p719_3 (m.d 3 4) (by simp) with h756 | h756
                          · linarith only [h560, h756, hlam]
                          · rcases p719_3 (m.d 3 5) (by simp) with h758 | h758
                            · linarith only [h758, hlam, p719_0]
                            · rcases h5bigk with h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c | h760c
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h562, h6, h8, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p760_1, u1ehi3]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                rcases p760_3 (m.d 0 5) (by simp) with h763 | h763
                                · rcases p760_3 (m.d 1 5) (by simp) with h764 | h764
                                  · linarith only [h3, h764, hlam]
                                  · linarith only [h559, h764, hlam]
                                · linarith only [h5, h763, hlam]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                rcases p760_3 (m.d 0 5) (by simp) with h768 | h768
                                · rcases p760_3 (m.d 1 5) (by simp) with h769 | h769
                                  · linarith only [h3, h769, hlam]
                                  · linarith only [h561, h769, hlam]
                                · linarith only [h7, h768, hlam]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h0, h4, h562, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p760_1, u1ehi3]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h3, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h3, h715, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h4, h559, h717, h9, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h562, hlam, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h5, hlam, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h559, hlam, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h0, h5, h717, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h715, hlam, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h7, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h561, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h714, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h717, hlam, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h8, hlam, p760_0]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p760_1, u1ehi4]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h0, h4, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [h0, h4, h6, h717, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p760_1]
                              · have p760_0 := h760c.1
                                have p760_1 := h760c.2.1
                                have p760_2 := h760c.2.2.1
                                have p760_3 := h760c.2.2.2
                                linarith only [hlam, p760_0]
                        · linarith only [h714, h755, hlam]
                      · linarith only [h754, hlam, p719_0]
                    · linarith only [h7, h753, hlam]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h4, hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p719_1, u1ehi2]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    rcases p719_3 (m.d 0 3) (by simp) with h800 | h800
                    · rcases p719_3 (m.d 1 3) (by simp) with h801 | h801
                      · linarith only [h801, h9, hlam]
                      · linarith only [h560, h801, hlam]
                    · linarith only [h6, h800, hlam]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    rcases p719_3 (m.d 0 3) (by simp) with h805 | h805
                    · rcases p719_3 (m.d 1 3) (by simp) with h806 | h806
                      · linarith only [h806, h9, hlam]
                      · linarith only [h561, h806, hlam]
                    · linarith only [h7, h805, hlam]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h6, hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h560, hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h713, hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h717, hlam, p719_1]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h7, hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h561, hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h714, hlam, p719_0]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [h0, h559, h714, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p719_1]
                  · have p719_0 := h719c.1
                    have p719_1 := h719c.2.1
                    have p719_2 := h719c.2.2.1
                    have p719_3 := h719c.2.2.2
                    linarith only [hlam, p719_0]
            · linarith only [h714, h9, hc35, hlam, hphi, ht12, ht23, u1ehi1]
          · linarith only [h559, h562, h713, h9, hc34, hlam, hphi, ht12, ht23, u1ehi3]
      · linarith only [h559, h561, h9, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h823 | h823
      · rcases m.htr 1 4 5 (by decide) (by decide) with h824 | h824
        · rcases m.htr 2 3 4 (by decide) (by decide) with h825 | h825
          · linarith only [h0, h4, h559, h560, h825, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
          · linarith only [h559, h825, h9, hc34, hlam, hphi, ht12, ht23, u1ehi4]
        · linarith only [h559, h560, h824, h9, hlam]
      · linarith only [h559, h823, h9, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h830 | h830
    · rcases m.htr 1 3 5 (by decide) (by decide) with h831 | h831
      · rcases m.htr 1 4 5 (by decide) (by decide) with h832 | h832
        · rcases m.htr 2 3 4 (by decide) (by decide) with h833 | h833
          · rcases m.htr 2 3 5 (by decide) (by decide) with h834 | h834
            · rcases m.htr 2 4 5 (by decide) (by decide) with h835 | h835
              · rcases m.htr 3 4 5 (by decide) (by decide) with h836 | h836
                · rcases h3bigk with h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h0, h4, h830, h836, hc01, hc45, hlam, hphi, ht0b, ht5b, p837_1]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h0, h4, h559, h833, h835, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p837_1, u1ehi1]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    rcases p837_3 (m.d 0 3) (by simp) with h841 | h841
                    · rcases p837_3 (m.d 1 3) (by simp) with h842 | h842
                      · linarith only [h1, h842, hlam]
                      · linarith only [h830, h842, hlam]
                    · linarith only [h841, hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    rcases p837_3 (m.d 0 3) (by simp) with h846 | h846
                    · rcases p837_3 (m.d 1 3) (by simp) with h847 | h847
                      · linarith only [h1, h847, hlam]
                      · linarith only [h831, h847, hlam]
                    · linarith only [h846, hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h1, hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h9, hlam, p837_1]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h1, h836, hc01, hc45, hlam, hphi, ht0b, ht5b, p837_1]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    rcases p837_3 (m.d 0 3) (by simp) with h855 | h855
                    · rcases p837_3 (m.d 1 3) (by simp) with h856 | h856
                      · rcases p837_3 (m.d 2 3) (by simp) with h857 | h857
                        · rcases p837_3 (m.d 3 4) (by simp) with h858 | h858
                          · linarith only [h830, h858, hlam]
                          · linarith only [h836, h858, hlam]
                        · linarith only [h834, h857, hlam]
                      · linarith only [h856, hlam, p837_0]
                    · linarith only [h7, h855, hlam]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h4, hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p837_1, u1ehi2]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h0, h4, h836, hc01, hc45, hlam, hphi, ht0b, ht5b, p837_1]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    rcases p837_3 (m.d 0 3) (by simp) with h868 | h868
                    · rcases p837_3 (m.d 1 3) (by simp) with h869 | h869
                      · linarith only [h869, h9, hlam]
                      · linarith only [h831, h869, hlam]
                    · linarith only [h7, h868, hlam]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h6, hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h830, hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h833, hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h1, h830, h836, hc01, hc45, hlam, hphi, ht0b, ht5b, p837_1]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h7, hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h831, hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h834, hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [h836, hlam, p837_0]
                  · have p837_0 := h837c.1
                    have p837_1 := h837c.2.1
                    have p837_2 := h837c.2.2.1
                    have p837_3 := h837c.2.2.2
                    linarith only [hlam, p837_0]
                · rcases h3bigk with h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h0, h4, h830, h832, h836, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p883_1, u1ehi1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    rcases p883_3 (m.d 0 3) (by simp) with h887 | h887
                    · rcases p883_3 (m.d 1 3) (by simp) with h888 | h888
                      · linarith only [h1, h888, hlam]
                      · linarith only [h830, h888, hlam]
                    · linarith only [h887, hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    rcases p883_3 (m.d 0 3) (by simp) with h892 | h892
                    · rcases p883_3 (m.d 1 3) (by simp) with h893 | h893
                      · linarith only [h1, h893, hlam]
                      · linarith only [h831, h893, hlam]
                    · linarith only [h892, hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h1, hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h9, hlam, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    rcases p883_3 (m.d 0 3) (by simp) with h900 | h900
                    · rcases p883_3 (m.d 1 3) (by simp) with h901 | h901
                      · rcases p883_3 (m.d 2 3) (by simp) with h902 | h902
                        · rcases p883_3 (m.d 3 4) (by simp) with h903 | h903
                          · linarith only [h903, hlam, p883_0]
                          · rcases p883_3 (m.d 3 5) (by simp) with h905 | h905
                            · linarith only [h831, h905, hlam]
                            · linarith only [h836, h905, hlam]
                        · linarith only [h833, h902, hlam]
                      · linarith only [h901, hlam, p883_0]
                    · linarith only [h6, h900, hlam]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    rcases p883_3 (m.d 0 3) (by simp) with h911 | h911
                    · rcases p883_3 (m.d 1 3) (by simp) with h912 | h912
                      · rcases p883_3 (m.d 2 3) (by simp) with h913 | h913
                        · rcases p883_3 (m.d 3 4) (by simp) with h914 | h914
                          · linarith only [h830, h914, hlam]
                          · rcases p883_3 (m.d 3 5) (by simp) with h916 | h916
                            · linarith only [h916, hlam, p883_0]
                            · rcases h5bigk with h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h6, h8, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p918_1, u1ehi4]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h0, h4, h559, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p918_1, u1ehi1]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                rcases p918_3 (m.d 0 5) (by simp) with h922 | h922
                                · rcases p918_3 (m.d 1 5) (by simp) with h923 | h923
                                  · linarith only [h3, h923, hlam]
                                  · linarith only [h831, h923, hlam]
                                · linarith only [h7, h922, hlam]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h0, h4, h6, h8, h836, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p918_1]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h3, hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h559, hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p918_1]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h836, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p918_1]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h5, hlam, p918_1]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h835, hc24, hlam, hphi, ht12, p918_1, u1ehi4]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h0, h4, h834, hc01, hc35, hlam, hphi, ht0b, ht5b, p918_1]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h0, h4, h833, h835, h836, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p918_1]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h7, hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h831, hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h834, hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h836, hlam, p918_1]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h8, hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h832, hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h835, hlam, p918_0]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [h0, h4, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b, p918_1]
                              · have p918_0 := h918c.1
                                have p918_1 := h918c.2.1
                                have p918_2 := h918c.2.2.1
                                have p918_3 := h918c.2.2.2
                                linarith only [hlam, p918_0]
                        · linarith only [h834, h913, hlam]
                      · linarith only [h912, hlam, p883_0]
                    · linarith only [h7, h911, hlam]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h4, hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p883_1, u1ehi2]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    rcases p883_3 (m.d 0 3) (by simp) with h954 | h954
                    · rcases p883_3 (m.d 1 3) (by simp) with h955 | h955
                      · linarith only [h9, h955, hlam]
                      · linarith only [h830, h955, hlam]
                    · linarith only [h6, h954, hlam]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    rcases p883_3 (m.d 0 3) (by simp) with h959 | h959
                    · rcases p883_3 (m.d 1 3) (by simp) with h960 | h960
                      · linarith only [h9, h960, hlam]
                      · linarith only [h831, h960, hlam]
                    · linarith only [h7, h959, hlam]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h6, hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h830, hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h833, hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h836, hlam, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h7, hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h831, hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h834, hlam, p883_0]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [h0, h4, h831, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p883_1]
                  · have p883_0 := h883c.1
                    have p883_1 := h883c.2.1
                    have p883_2 := h883c.2.2.1
                    have p883_3 := h883c.2.2.2
                    linarith only [hlam, p883_0]
              · linarith only [h0, h4, h559, h830, h832, h835, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
            · linarith only [h0, h4, h7, h834, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · linarith only [h833, h9, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h977 | h977
          · rcases m.htr 2 3 5 (by decide) (by decide) with h978 | h978
            · rcases m.htr 2 4 5 (by decide) (by decide) with h979 | h979
              · linarith only [h832, h979, hc24, hlam, hphi, ht12, u1ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h981 | h981
                · linarith only [h1, h830, h979, h981, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h3bigk with h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    rcases p983_3 (m.d 0 3) (by simp) with h985 | h985
                    · rcases p983_3 (m.d 1 3) (by simp) with h986 | h986
                      · linarith only [h1, h986, hlam]
                      · rcases p983_3 (m.d 2 3) (by simp) with h988 | h988
                        · linarith only [h4, h988, hlam]
                        · linarith only [h9, h988, hlam]
                    · linarith only [h1, h985, hlam]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p983_1, u1ehi1]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    rcases p983_3 (m.d 0 3) (by simp) with h993 | h993
                    · rcases p983_3 (m.d 1 3) (by simp) with h994 | h994
                      · linarith only [h1, h994, hlam]
                      · linarith only [h830, h994, hlam]
                    · linarith only [h993, hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    rcases p983_3 (m.d 0 3) (by simp) with h998 | h998
                    · rcases p983_3 (m.d 1 3) (by simp) with h999 | h999
                      · linarith only [h1, h999, hlam]
                      · linarith only [h831, h999, hlam]
                    · linarith only [h998, hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h1, hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h9, hlam, p983_1]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    rcases p983_3 (m.d 0 3) (by simp) with h1006 | h1006
                    · rcases p983_3 (m.d 1 3) (by simp) with h1007 | h1007
                      · rcases p983_3 (m.d 2 3) (by simp) with h1008 | h1008
                        · rcases p983_3 (m.d 3 4) (by simp) with h1009 | h1009
                          · linarith only [h1009, hlam, p983_0]
                          · rcases p983_3 (m.d 3 5) (by simp) with h1011 | h1011
                            · linarith only [h1011, h831, hlam]
                            · linarith only [h1011, h981, hlam]
                        · linarith only [h1008, h977, hlam]
                      · linarith only [h1007, hlam, p983_0]
                    · linarith only [h1006, h6, hlam]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    rcases p983_3 (m.d 0 3) (by simp) with h1017 | h1017
                    · rcases p983_3 (m.d 1 3) (by simp) with h1018 | h1018
                      · rcases p983_3 (m.d 2 3) (by simp) with h1019 | h1019
                        · rcases p983_3 (m.d 3 4) (by simp) with h1020 | h1020
                          · linarith only [h1020, h830, hlam]
                          · rcases p983_3 (m.d 3 5) (by simp) with h1022 | h1022
                            · linarith only [h1022, hlam, p983_0]
                            · rcases h5bigk with h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c | h1024c
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [hlam, p1024_0]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h0, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1024_1, u1ehi4]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h0, h4, h559, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1024_1, u1ehi1]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                rcases p1024_3 (m.d 0 5) (by simp) with h1028 | h1028
                                · rcases p1024_3 (m.d 1 5) (by simp) with h1029 | h1029
                                  · linarith only [h1029, h3, hlam]
                                  · linarith only [h1029, h831, hlam]
                                · linarith only [h1028, h7, hlam]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h0, h4, h6, h8, h832, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1024_1]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h3, hlam, p1024_0]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [hlam, p1024_0]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h559, hlam, p1024_0]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h3, h981, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1024_1]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h832, hlam, p1024_1]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h5, hlam, p1024_1]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [hc25, hlam, hphi, ht12, p1024_1, u1ehi4]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [hlam, p1024_0]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h0, h4, h978, h981, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1024_1]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h979, hlam, p1024_1]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h7, hlam, p1024_0]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h831, hlam, p1024_0]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h978, hlam, p1024_0]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [hlam, p1024_0]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h981, hlam, p1024_1]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h8, hlam, p1024_0]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h559, hc45, hlam, hphi, ht12, ht23, ht34, p1024_1, u1ehi1]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h0, h4, h6, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p1024_1]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [h0, h4, h6, h8, h981, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1024_1]
                              · have p1024_0 := h1024c.1
                                have p1024_1 := h1024c.2.1
                                have p1024_2 := h1024c.2.2.1
                                have p1024_3 := h1024c.2.2.2
                                linarith only [hlam, p1024_0]
                        · linarith only [h1019, h978, hlam]
                      · linarith only [h1018, hlam, p983_0]
                    · linarith only [h1017, h7, hlam]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h4, hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p983_1, u1ehi2]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    rcases p983_3 (m.d 0 3) (by simp) with h1060 | h1060
                    · rcases p983_3 (m.d 1 3) (by simp) with h1061 | h1061
                      · linarith only [h1061, h9, hlam]
                      · linarith only [h1061, h830, hlam]
                    · linarith only [h1060, h6, hlam]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    rcases p983_3 (m.d 0 3) (by simp) with h1065 | h1065
                    · rcases p983_3 (m.d 1 3) (by simp) with h1066 | h1066
                      · linarith only [h1066, h9, hlam]
                      · linarith only [h1066, h831, hlam]
                    · linarith only [h1065, h7, hlam]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h6, hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h830, hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h977, hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h981, hlam, p983_1]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h7, hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h831, hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h978, hlam, p983_0]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [h1, h831, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p983_1]
                  · have p983_0 := h983c.1
                    have p983_1 := h983c.2.1
                    have p983_2 := h983c.2.2.1
                    have p983_3 := h983c.2.2.2
                    linarith only [hlam, p983_0]
            · linarith only [h0, h4, h7, h9, h978, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · linarith only [h9, h977, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1082 | h1082
        · linarith only [h1082, h830, h831, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1084 | h1084
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1085 | h1085
            · linarith only [h1085, h831, h9, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h0, h1085, h4, h7, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · linarith only [h1084, h830, h9, hc13, hlam, hphi, u1ehi1]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1089 | h1089
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1090 | h1090
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1091 | h1091
          · linarith only [h0, h1089, h1091, h4, h830, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h1091, h9, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h1089, h1090, h830, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1095 | h1095
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1096 | h1096
          · linarith only [h1096, h830, hc23, hlam, hphi, ht12, u1ehi2]
          · linarith only [h0, h1096, h4, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1099 | h1099
          · linarith only [h1099, h830, hc23, hlam, hphi, ht12, u1ehi2]
          · linarith only [h1099, h9, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 5130000 in
set_option maxHeartbeats 5130000 in
theorem r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1ehi := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9
  · exact r1l7_11_13_25_L_R_L_I_H_I_s3_x0_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9

end R2N4
