import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_19S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10468000 in
set_option maxHeartbeats 10468000 in
theorem r1l7_21_14_H_I_L_I_s0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_21_14_H_I_L_I_s1 m hb1 hb4 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h4617 | h4617
    · rcases m.htr 0 1 5 (by decide) (by decide) with h4618 | h4618
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4619 | h4619
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4620 | h4620
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4621 | h4621
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4622 | h4622
              · linarith only [h0, h1, h4622, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4624 | h4624
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4625 | h4625
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4626 | h4626
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4627 | h4627
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4628 | h4628
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4629 | h4629
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4630 | h4630
                            · linarith only [h0, h1, h4624, h4630, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h1, h4622, h4624, h4628, h4629, h4630, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h1, h4622, h4629, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4634 | h4634
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4635 | h4635
                            · linarith only [h4624, h4628, h4635, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4637 | h4637
                              · linarith only [h4624, h4628, h4634, h4637, hlam]
                              · rcases h1bigk with h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c | h4639c
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [hlam, p4639_0]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4639_1]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h1, hlam, p4639_0]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h1, h4622, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4639_1]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h1, h4622, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4639_1]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h0, hlam, p4639_0]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [hlam, p4639_0]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h4622, hlam, p4639_1]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h0, h1, h4622, h4624, h4634, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4639_1]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h0, h1, h4622, h4627, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p4639_1]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h4622, hc01, hc23, hlam, hphi, ht12, p4639_1]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h4622, hc12, hc23, hlam, hphi, p4639_1]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [hlam, p4639_0]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  rcases p4639_3 (m.d 0 1) (by simp) with h4653 | h4653
                                  · linarith only [h1, h4653, hlam]
                                  · linarith only [h4617, h4653, hlam]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  rcases p4639_3 (m.d 0 1) (by simp) with h4656 | h4656
                                  · linarith only [h1, h4656, hlam]
                                  · linarith only [h4618, h4656, hlam]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h4617, hlam, p4639_0]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h4624, hlam, p4639_0]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h4626, hlam, p4639_1]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [hlam, p4639_0]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h4628, hlam, p4639_1]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h4618, hlam, p4639_0]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h4625, hlam, p4639_0]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h4627, hlam, p4639_0]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [h1, h4618, h4622, h4624, h4634, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4639_1]
                                · have p4639_0 := h4639c.1
                                  have p4639_1 := h4639c.2.1
                                  have p4639_2 := h4639c.2.2.1
                                  have p4639_3 := h4639c.2.2.2
                                  linarith only [hlam, p4639_0]
                          · linarith only [h0, h1, h4622, h4634, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h4624, h4627, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h4624, h4626, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4672 | h4672
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4673 | h4673
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4674 | h4674
                        · linarith only [h4624, h4625, h4674, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4676 | h4676
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4677 | h4677
                            · linarith only [h4624, h4625, h4674, h4677, hlam]
                            · linarith only [h0, h1, h4619, h4621, h4622, h4624, h4625, h4676, h4677, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h1, h4622, h4676, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h4618, h4624, h4625, h4673, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1, h4618, h4624, h4625, h4672, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h4619, h4622, h4624, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4684 | h4684
              · linarith only [h0, h1, h4684, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4686 | h4686
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4687 | h4687
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4688 | h4688
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4689 | h4689
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4690 | h4690
                        · linarith only [h4617, h4621, h4690, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4692 | h4692
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4693 | h4693
                            · linarith only [h0, h1, h4621, h4684, h4686, h4693, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4695 | h4695
                              · linarith only [h4617, h4621, h4686, h4692, h4695, hlam]
                              · rcases h1bigk with h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c | h4697c
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [hlam, p4697_0]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h1, h4684, h4687, h4692, h4693, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4697_1]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h1, hlam, p4697_0]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h1, h4684, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4697_1]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h1, h4684, h4690, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4697_1]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h0, hlam, p4697_0]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [hlam, p4697_0]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h4684, hlam, p4697_1]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h0, h1, h4684, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4697_1]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h0, h1, h4684, h4686, h4690, h4692, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4697_1]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h4684, hc01, hc23, hlam, hphi, ht12, p4697_1]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h4684, hc12, hc23, hlam, hphi, p4697_1]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [hlam, p4697_0]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  rcases p4697_3 (m.d 0 1) (by simp) with h4711 | h4711
                                  · linarith only [h1, h4711, hlam]
                                  · linarith only [h4617, h4711, hlam]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  rcases p4697_3 (m.d 0 1) (by simp) with h4714 | h4714
                                  · linarith only [h1, h4714, hlam]
                                  · linarith only [h4618, h4714, hlam]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h4617, hlam, p4697_0]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h4686, hlam, p4697_0]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h4688, hlam, p4697_1]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [hlam, p4697_0]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h4690, hlam, p4697_1]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h4618, hlam, p4697_0]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h4687, hlam, p4697_0]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h4689, hlam, p4697_0]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [h4618, h4686, h4692, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4697_1]
                                · have p4697_0 := h4697c.1
                                  have p4697_1 := h4697c.2.1
                                  have p4697_2 := h4697c.2.2.1
                                  have p4697_3 := h4697c.2.2.2
                                  linarith only [hlam, p4697_0]
                          · linarith only [h0, h1, h4684, h4687, h4692, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h1, h4686, h4689, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h4686, h4688, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4730 | h4730
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4731 | h4731
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4732 | h4732
                        · linarith only [h1, h4618, h4621, h4686, h4687, h4732, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4734 | h4734
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4735 | h4735
                            · linarith only [h1, h4617, h4618, h4621, h4684, h4686, h4687, h4735, hc12, hc23, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4737 | h4737
                              · linarith only [h1, h4620, h4684, h4687, h4735, h4737, hc12, hc23, hlam, hphi]
                              · rcases h1bigk with h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c | h4739c
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [hlam, p4739_0]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h1, h4684, h4686, h4734, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h1, hlam, p4739_0]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h1, h4684, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h1, h4684, h4686, h4687, h4734, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h0, hlam, p4739_0]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [hlam, p4739_0]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4684, hlam, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4687, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4687, hlam, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4684, hc01, hc23, hlam, hphi, ht12, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4684, hc12, hc23, hlam, hphi, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [hlam, p4739_0]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  rcases p4739_3 (m.d 0 1) (by simp) with h4753 | h4753
                                  · linarith only [h1, h4753, hlam]
                                  · linarith only [h4617, h4753, hlam]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4684, h4686, h4687, h4734, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4617, hlam, p4739_0]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4686, hlam, p4739_0]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4730, hlam, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [hlam, p4739_0]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4732, hlam, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4618, hlam, p4739_0]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4686, h4734, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h4731, hlam, p4739_0]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [h1, h4618, h4684, h4686, h4734, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4739_1]
                                · have p4739_0 := h4739c.1
                                  have p4739_1 := h4739c.2.1
                                  have p4739_2 := h4739c.2.2.1
                                  have p4739_3 := h4739c.2.2.2
                                  linarith only [hlam, p4739_0]
                          · linarith only [h0, h1, h4684, h4734, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h4618, h4686, h4687, h4731, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1, h4618, h4686, h4687, h4730, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h4619, h4684, h4686, hc12, hc23, hlam, hphi]
          · linarith only [h0, h1, h4619, h4620, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4772 | h4772
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4773 | h4773
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4774 | h4774
              · linarith only [h0, h1, h4774, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4776 | h4776
                · linarith only [h0, h1, h4619, h4776, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4778 | h4778
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4779 | h4779
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4780 | h4780
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4781 | h4781
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4782 | h4782
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4783 | h4783
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4784 | h4784
                              · rcases h1bigk with h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c | h4785c
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [hlam, p4785_0]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h1, h4774, h4778, h4783, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h1, hlam, p4785_0]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h1, h4774, h4776, h4778, h4783, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h1, h4774, h4778, h4783, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h0, hlam, p4785_0]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [hlam, p4785_0]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4774, hlam, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4776, hlam, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h0, h1, h4774, h4778, h4783, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4774, hc01, hc23, hlam, hphi, ht12, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4774, hc12, hc23, hlam, hphi, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [hlam, p4785_0]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4774, h4776, h4778, h4783, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  rcases p4785_3 (m.d 0 1) (by simp) with h4800 | h4800
                                  · linarith only [h1, h4800, hlam]
                                  · linarith only [h4618, h4800, hlam]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4617, hlam, p4785_0]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4778, h4783, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4779, hlam, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [hlam, p4785_0]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h1, h4617, h4774, h4778, h4783, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4785_1]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4618, hlam, p4785_0]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4778, hlam, p4785_0]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4780, hlam, p4785_0]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [h4781, hlam, p4785_0]
                                · have p4785_0 := h4785c.1
                                  have p4785_1 := h4785c.2.1
                                  have p4785_2 := h4785c.2.2.1
                                  have p4785_3 := h4785c.2.2.2
                                  linarith only [hlam, p4785_0]
                              · linarith only [h0, h1, h4774, h4778, h4783, h4784, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h1, h4617, h4774, h4781, h4783, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h1, h4617, h4774, h4776, h4782, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h1, h4617, h4773, h4776, h4778, h4781, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h1, h4778, h4780, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1, h4617, h4776, h4778, h4779, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4819 | h4819
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4820 | h4820
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4821 | h4821
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4822 | h4822
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4823 | h4823
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4824 | h4824
                              · rcases h1bigk with h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c | h4825c
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [hlam, p4825_0]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h1, hlam, p4825_0]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h1, h4819, h4824, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h1, h4778, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h0, hlam, p4825_0]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [hlam, p4825_0]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4774, hlam, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4776, hlam, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4778, hlam, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [hc01, hc13, hlam, hphi, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4774, hc12, hc23, hlam, hphi, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [hlam, p4825_0]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4774, h4819, h4824, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4774, h4778, hc12, hc23, hlam, hphi, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4617, hlam, p4825_0]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4617, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4819, hlam, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [hlam, p4825_0]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h1, h4617, h4774, h4778, hc12, hc23, hlam, hphi, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4618, hlam, p4825_0]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h1, h4618, h4774, hc12, hc23, hlam, hphi, p4825_1]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4820, hlam, p4825_0]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [h4821, hlam, p4825_0]
                                · have p4825_0 := h4825c.1
                                  have p4825_1 := h4825c.2.1
                                  have p4825_2 := h4825c.2.2.1
                                  have p4825_3 := h4825c.2.2.2
                                  linarith only [hlam, p4825_0]
                              · linarith only [h1, h4617, h4774, h4821, h4824, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h1, h4617, h4774, h4821, h4823, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h1, h4617, h4774, h4821, h4822, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h4617, h4773, h4774, h4776, h4821, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h4820, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h4617, h4776, h4819, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4857 | h4857
              · linarith only [h0, h1, h4857, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4859 | h4859
                · linarith only [h0, h1, h4619, h4857, h4859, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4861 | h4861
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4862 | h4862
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4863 | h4863
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4864 | h4864
                        · linarith only [h1, h4617, h4773, h4857, h4864, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h4859, h4861, h4864, hlam]
                      · linarith only [h0, h1, h4861, h4863, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1, h4617, h4859, h4861, h4862, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4869 | h4869
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4870 | h4870
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4871 | h4871
                        · linarith only [h1, h4617, h4619, h4773, h4871, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4873 | h4873
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4874 | h4874
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4875 | h4875
                              · linarith only [h4617, h4773, h4869, h4875, hlam]
                              · rcases h1bigk with h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c | h4877c
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [hlam, p4877_0]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h1, h4857, hc12, hc23, hlam, hphi, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h1, hlam, p4877_0]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h1, h4857, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h1, h4857, h4869, h4871, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h0, hlam, p4877_0]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [hlam, p4877_0]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4857, hlam, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4859, hlam, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4861, hlam, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4857, hc01, hc23, hlam, hphi, ht12, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4857, hc12, hc23, hlam, hphi, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [hlam, p4877_0]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4857, h4859, hc12, hc23, hlam, hphi, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4857, h4859, h4871, hc12, hc23, hlam, hphi, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4617, hlam, p4877_0]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4618, h4871, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4869, hlam, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [hlam, p4877_0]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4871, hlam, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4618, hlam, p4877_0]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h1, h4618, h4857, hc12, hc23, hlam, hphi, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h4870, hlam, p4877_0]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [h1, h4618, h4857, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4877_1]
                                · have p4877_0 := h4877c.1
                                  have p4877_1 := h4877c.2.1
                                  have p4877_2 := h4877c.2.2.1
                                  have p4877_3 := h4877c.2.2.2
                                  linarith only [hlam, p4877_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4903 | h4903
                              · linarith only [h0, h4619, h4874, h4903, hc12, hc34, hlam, hphi, ht23]
                              · rcases h1bigk with h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [hlam, p4905_0]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h1, h4857, hc12, hc23, hlam, hphi, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h1, hlam, p4905_0]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h1, h4857, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h1, h4857, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h0, hlam, p4905_0]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [hlam, p4905_0]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4857, hlam, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4859, hlam, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4861, hlam, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4857, hc01, hc23, hlam, hphi, ht12, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4857, hc12, hc23, hlam, hphi, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [hlam, p4905_0]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4857, h4859, hc12, hc23, hlam, hphi, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4857, h4861, hc12, hc23, hlam, hphi, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4617, hlam, p4905_0]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4617, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4869, hlam, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [hlam, p4905_0]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4871, hlam, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4618, hlam, p4905_0]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h1, h4618, h4857, hc12, hc23, hlam, hphi, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h4870, hlam, p4905_0]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [h1, h4618, h4857, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4905_1]
                                · have p4905_0 := h4905c.1
                                  have p4905_1 := h4905c.2.1
                                  have p4905_2 := h4905c.2.2.1
                                  have p4905_3 := h4905c.2.2.2
                                  linarith only [hlam, p4905_0]
                          · linarith only [h0, h1, h4857, h4873, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h4617, h4859, h4870, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h4617, h4859, h4869, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1, h4617, h4772, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4935 | h4935
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4936 | h4936
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4937 | h4937
            · linarith only [h0, h4618, h4935, h4937, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4939 | h4939
              · linarith only [h0, h1, h4939, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4941 | h4941
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4942 | h4942
                  · linarith only [h0, h4618, h4942, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4944 | h4944
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4945 | h4945
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4946 | h4946
                        · linarith only [h4617, h4618, h4937, h4945, h4946, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h4618, h4941, h4946, hc24, hc45, hlam, hphi]
                      · linarith only [h0, h1, h4941, h4945, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h4941, h4944, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h4935, h4939, h4941, hc12, hc23, hlam, hphi]
          · linarith only [h1, h4617, h4936, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4953 | h4953
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4954 | h4954
            · linarith only [h4617, h4618, h4954, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4956 | h4956
              · linarith only [h0, h1, h4956, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4958 | h4958
                · linarith only [h0, h1, h4935, h4958, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4960 | h4960
                  · linarith only [h0, h4618, h4960, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4962 | h4962
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4963 | h4963
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4964 | h4964
                        · linarith only [h4617, h4618, h4954, h4964, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4966 | h4966
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4967 | h4967
                            · linarith only [h4617, h4618, h4958, h4964, h4967, hc12, hc24, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4969 | h4969
                              · linarith only [h4617, h4618, h4962, h4963, h4967, h4969, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases h1bigk with h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [hlam, p4971_0]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4618, h4960, h4967, hc12, hc45, hlam, hphi, ht23, ht34, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h1, hlam, p4971_0]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4618, h4960, h4967, hc14, hc45, hlam, hphi, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4618, hlam, p4971_0]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h0, hlam, p4971_0]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [hlam, p4971_0]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4956, hlam, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4958, hlam, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4960, hlam, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4956, hc01, hc23, hlam, hphi, ht12, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4956, hc12, hc23, hlam, hphi, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [hlam, p4971_0]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4956, h4958, hc12, hc23, hlam, hphi, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4618, h4956, hc01, hc23, hlam, hphi, ht12, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4617, hlam, p4971_0]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4617, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4962, hlam, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [hlam, p4971_0]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4964, hlam, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [hc01, hc15, hlam, hphi, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4960, h4967, hc12, hc45, hlam, hphi, ht23, ht34, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4963, hlam, p4971_0]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [h4958, h4960, h4967, hc12, hc45, hlam, hphi, ht23, ht34, p4971_1]
                                · have p4971_0 := h4971c.1
                                  have p4971_1 := h4971c.2.1
                                  have p4971_2 := h4971c.2.2.1
                                  have p4971_3 := h4971c.2.2.2
                                  linarith only [hlam, p4971_0]
                          · linarith only [h1, h4617, h4956, h4958, h4966, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h4617, h4958, h4963, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h4617, h4958, h4962, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1, h4617, h4953, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h5001 | h5001
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5002 | h5002
        · linarith only [h0, h4617, h5002, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5004 | h5004
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5005 | h5005
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5006 | h5006
              · linarith only [h0, h1, h5006, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5008 | h5008
                · linarith only [h0, h1, h5002, h5008, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5010 | h5010
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5011 | h5011
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5012 | h5012
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5013 | h5013
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5014 | h5014
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5015 | h5015
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5016 | h5016
                              · rcases h1bigk with h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c | h5017c
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [hlam, p5017_0]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h4617, h5006, h5010, h5011, h5015, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5017_1]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h1, hlam, p5017_0]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h4617, hlam, p5017_0]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h4617, h5006, h5010, h5011, h5015, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5017_1]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h0, hlam, p5017_0]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [hlam, p5017_0]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h5006, hlam, p5017_1]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h5008, hlam, p5017_1]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h0, h4617, h5006, h5010, h5011, h5015, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5017_1]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h5006, hc01, hc23, hlam, hphi, ht12, p5017_1]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h5006, hc12, hc23, hlam, hphi, p5017_1]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [hlam, p5017_0]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h0, h4617, h5006, hc12, hc23, hlam, hphi, p5017_1]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  rcases p5017_3 (m.d 0 1) (by simp) with h5032 | h5032
                                  · linarith only [h1, h5032, hlam]
                                  · linarith only [h5001, h5032, hlam]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h0, h5010, h5015, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p5017_1]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h5008, h5010, h5015, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5017_1]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h5011, hlam, p5017_1]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [hlam, p5017_0]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  rcases p5017_3 (m.d 0 1) (by simp) with h5039 | h5039
                                  · linarith only [h4617, h5039, hlam]
                                  · linarith only [h5001, h5039, hlam]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h5001, hlam, p5017_0]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h5010, hlam, p5017_0]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h5012, hlam, p5017_0]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [h5013, hlam, p5017_0]
                                · have p5017_0 := h5017c.1
                                  have p5017_1 := h5017c.2.1
                                  have p5017_2 := h5017c.2.2.1
                                  have p5017_3 := h5017c.2.2.2
                                  linarith only [hlam, p5017_0]
                              · linarith only [h0, h1, h5006, h5010, h5015, h5016, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h5002, h5005, h5015, hlam]
                          · linarith only [h0, h1, h5006, h5010, h5014, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h4617, h5010, h5013, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h0, h4617, h5010, h5011, h5012, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1, h5004, h5011, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5053 | h5053
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5054 | h5054
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5055 | h5055
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5056 | h5056
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5057 | h5057
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5058 | h5058
                              · rcases h1bigk with h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c | h5059c
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [hlam, p5059_0]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h4617, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h1, hlam, p5059_0]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h4617, hlam, p5059_0]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h4617, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h0, hlam, p5059_0]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [hlam, p5059_0]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5006, hlam, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5008, hlam, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5010, hlam, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5006, hc01, hc23, hlam, hphi, ht12, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5006, hc12, hc23, hlam, hphi, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [hlam, p5059_0]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h4617, h5001, h5006, h5010, hc12, hc23, hlam, hphi, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5006, h5010, hc12, hc23, hlam, hphi, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5001, h5010, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5008, hc12, hc24, hlam, hphi, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5053, hlam, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [hlam, p5059_0]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5006, h5010, h5053, hc12, hc23, hlam, hphi, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5001, hlam, p5059_0]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5001, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5059_1]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5054, hlam, p5059_0]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [h5055, hlam, p5059_0]
                                · have p5059_0 := h5059c.1
                                  have p5059_1 := h5059c.2.1
                                  have p5059_2 := h5059c.2.2.1
                                  have p5059_3 := h5059c.2.2.2
                                  linarith only [hlam, p5059_0]
                              · rcases h1bigk with h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c | h5085c
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [hlam, p5085_0]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h4617, h5006, h5053, hc12, hc23, hlam, hphi, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h1, hlam, p5085_0]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h4617, hlam, p5085_0]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h4617, h5006, h5053, h5055, h5058, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h0, hlam, p5085_0]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [hlam, p5085_0]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5006, hlam, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5008, hlam, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5010, hlam, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5006, hc01, hc23, hlam, hphi, ht12, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5006, hc12, hc23, hlam, hphi, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [hlam, p5085_0]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h4617, h5001, h5006, h5055, h5058, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5006, h5055, h5058, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5001, h5055, h5058, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5008, h5056, hc12, hc23, hlam, hphi, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5053, hlam, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [hlam, p5085_0]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5008, h5055, h5056, h5058, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5001, hlam, p5085_0]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5001, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5085_1]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5054, hlam, p5085_0]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [h5055, hlam, p5085_0]
                                · have p5085_0 := h5085c.1
                                  have p5085_1 := h5085c.2.1
                                  have p5085_2 := h5085c.2.2.1
                                  have p5085_3 := h5085c.2.2.2
                                  linarith only [hlam, p5085_0]
                            · linarith only [h4617, h5001, h5008, h5055, h5057, hlam]
                          · linarith only [h0, h1, h5006, h5056, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h4617, h5055, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h4617, h5001, h5010, h5053, h5054, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h5004, h5053, hlam]
            · linarith only [h4617, h5001, h5005, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5117 | h5117
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5118 | h5118
              · linarith only [h0, h1, h5004, h5118, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5120 | h5120
                · linarith only [h0, h1, h5002, h5004, h5120, hc02, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5122 | h5122
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5123 | h5123
                    · linarith only [h0, h1, h5004, h5118, h5123, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h5122, h5123, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5126 | h5126
                    · linarith only [h1, h5001, h5004, h5118, h5122, h5126, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h5001, h5122, h5126, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h5001, h5004, h5117, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5130 | h5130
        · linarith only [h0, h4617, h5130, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5132 | h5132
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5133 | h5133
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5134 | h5134
              · linarith only [h0, h1, h5134, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5136 | h5136
                · linarith only [h0, h1, h5130, h5136, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5138 | h5138
                  · linarith only [h0, h5001, h5138, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5140 | h5140
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5141 | h5141
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5142 | h5142
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5143 | h5143
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5144 | h5144
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5145 | h5145
                              · rcases h1bigk with h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c | h5146c
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [hlam, p5146_0]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5001, h5134, h5140, h5142, hc12, hc23, hlam, hphi, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h1, hlam, p5146_0]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h4617, hlam, p5146_0]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5001, hlam, p5146_0]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h0, hlam, p5146_0]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [hlam, p5146_0]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5134, hlam, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5136, hlam, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5138, hlam, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5134, hc01, hc23, hlam, hphi, ht12, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5134, hc12, hc23, hlam, hphi, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [hlam, p5146_0]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h0, h4617, h5134, hc12, hc23, hlam, hphi, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h0, h5001, h5134, hc12, hc23, hlam, hphi, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5136, hc12, hc24, hlam, hphi, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5140, hlam, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [hlam, p5146_0]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h0, h5001, h5134, h5140, hc12, hc23, hlam, hphi, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5138, hc12, hc25, hlam, hphi, p5146_1]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5141, hlam, p5146_0]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [h5142, hlam, p5146_0]
                                · have p5146_0 := h5146c.1
                                  have p5146_1 := h5146c.2.1
                                  have p5146_2 := h5146c.2.2.1
                                  have p5146_3 := h5146c.2.2.2
                                  linarith only [hlam, p5146_0]
                              · rcases h1bigk with h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [hlam, p5172_0]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h1, h5134, hc12, hc23, hlam, hphi, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h1, hlam, p5172_0]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h4617, hlam, p5172_0]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h5001, hlam, p5172_0]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h0, hlam, p5172_0]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [hlam, p5172_0]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h5134, hlam, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h5136, hlam, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h5138, hlam, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h5134, hc01, hc23, hlam, hphi, ht12, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h5134, hc12, hc23, hlam, hphi, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [hlam, p5172_0]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h4617, h5133, h5134, h5145, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h0, h5001, h5134, hc12, hc23, hlam, hphi, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h5136, h5143, hc12, hc23, hlam, hphi, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h5140, hlam, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [hlam, p5172_0]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h0, h5001, h5136, h5143, hc12, hc23, hlam, hphi, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h5138, h5143, h5144, hc12, hc23, hlam, hphi, p5172_1]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h5141, hlam, p5172_0]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [h5142, hlam, p5172_0]
                                · have p5172_0 := h5172c.1
                                  have p5172_1 := h5172c.2.1
                                  have p5172_2 := h5172c.2.2.1
                                  have p5172_3 := h5172c.2.2.2
                                  linarith only [hlam, p5172_0]
                            · linarith only [h0, h4617, h5132, h5133, h5136, h5144, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h1, h5134, h5143, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h4617, h5133, h5142, hlam]
                      · linarith only [h0, h1, h5141, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h5132, h5140, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5203 | h5203
              · linarith only [h0, h4617, h5133, h5203, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5205 | h5205
                · linarith only [h0, h4617, h5133, h5205, hc24, hc45, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5207 | h5207
                  · linarith only [h0, h5001, h5207, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5209 | h5209
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5210 | h5210
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5211 | h5211
                        · linarith only [h0, h4617, h5133, h5205, h5211, hc12, hc24, hlam, hphi]
                        · linarith only [h0, h4617, h5211, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h0, h1, h5210, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h5132, h5209, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5216 | h5216
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5217 | h5217
              · linarith only [h0, h1, h5132, h5217, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5219 | h5219
                · linarith only [h0, h5130, h5219, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5221 | h5221
                  · linarith only [h0, h5001, h5221, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5223 | h5223
                    · linarith only [h0, h1, h5132, h5217, h5223, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h5223, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5226 | h5226
              · linarith only [h0, h1, h5132, h5216, h5226, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5228 | h5228
                · linarith only [h0, h1, h5132, h5216, h5228, hc24, hc45, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5230 | h5230
                  · linarith only [h0, h5001, h5230, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5232 | h5232
                    · linarith only [h0, h1, h5132, h5226, h5232, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h5232, hc12, hc34, hlam, hphi, ht23]

end R2N4
