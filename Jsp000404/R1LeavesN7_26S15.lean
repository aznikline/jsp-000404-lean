import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_26S11
import Jsp000404.R1LeavesN7_26S12
import Jsp000404.R1LeavesN7_26S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_13_24_L_I_M_IR_s1_x1_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2760 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3404 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3607 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h4789 | h4789
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4790 | h4790
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4791 | h4791
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4792 | h4792
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4793 | h4793
          · linarith only [h3607, h4789, h4792, h4793, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4795 | h4795
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4796 | h4796
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4797 | h4797
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4798 | h4798
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4799 | h4799
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4800 | h4800
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4801 | h4801
                        · linarith only [h0, h4789, h4793, h4801, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h4789, h4792, h4793, h4799, h4801, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h4789, h4791, h4793, h4800, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h0, h4789, h4792, h4793, h4799, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h4789, h4792, h4793, h4798, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h2760, h4789, h4791, h4792, h4793, h4797, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h2760, h4790, h4796, hlam]
            · linarith only [h0, h4789, h4795, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4810 | h4810
          · linarith only [h3607, h4789, h4810, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4812 | h4812
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4813 | h4813
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4814 | h4814
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4815 | h4815
                  · linarith only [h4792, h4810, h4812, h4815, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4817 | h4817
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4818 | h4818
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4819 | h4819
                        · linarith only [h4789, h4815, h4819, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4821 | h4821
                          · linarith only [h3404, h4815, h4821, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h3bigk with h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c | h4823c
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h2760, hlam, p4823_1]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h3607, hlam, p4823_1]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              rcases p4823_3 (m.d 0 3) (by simp) with h4827 | h4827
                              · rcases p4823_3 (m.d 1 3) (by simp) with h4828 | h4828
                                · rcases p4823_3 (m.d 2 3) (by simp) with h4829 | h4829
                                  · rcases p4823_3 (m.d 3 4) (by simp) with h4830 | h4830
                                    · linarith only [h4830, hlam, p4823_0]
                                    · rcases p4823_3 (m.d 3 5) (by simp) with h4832 | h4832
                                      · linarith only [h4791, h4832, hlam]
                                      · linarith only [h4821, h4832, hlam]
                                  · linarith only [h4817, h4829, hlam]
                                · linarith only [h4813, h4828, hlam]
                              · linarith only [h4827, hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              rcases p4823_3 (m.d 0 3) (by simp) with h4838 | h4838
                              · rcases p4823_3 (m.d 1 3) (by simp) with h4839 | h4839
                                · rcases p4823_3 (m.d 2 3) (by simp) with h4840 | h4840
                                  · rcases p4823_3 (m.d 3 4) (by simp) with h4841 | h4841
                                    · linarith only [h4790, h4841, hlam]
                                    · rcases p4823_3 (m.d 3 5) (by simp) with h4843 | h4843
                                      · linarith only [h4843, hlam, p4823_0]
                                      · rcases h4bigk with h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c | h4845c
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [hlam, p4845_0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h3404, hlam, p4845_0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h3404, h4815, hc45, hlam, hphi, p4845_1, u4ehi2]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h3404, h4815, hc45, hlam, hphi, p4845_1, u4ehi3]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4792, hlam, p4845_0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4815, hc45, hlam, hphi, p4845_1, u4ehi0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [hlam, p4845_0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4815, hc45, hlam, hphi, p4845_1, u4ehi2]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4815, hc45, hlam, hphi, p4845_1, u4ehi3]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4815, hlam, p4845_0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4789, hlam, p4845_1]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4812, hlam, p4845_1]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [hlam, p4845_0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h3404, h4789, h4815, hc45, hlam, hphi, p4845_1, u4ehi3]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4819, hlam, p4845_0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4790, hlam, p4845_1]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4813, hlam, p4845_0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4817, hlam, p4845_0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [hlam, p4845_0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [h4821, hlam, p4845_0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [hc45, hlam, hphi, p4845_1, u4ehi0]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [hc45, hlam, hphi, p4845_1, u4ehi1]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [hc45, hlam, hphi, p4845_1, u4ehi2]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [hc45, hlam, hphi, p4845_1, u4ehi3]
                                        · have p4845_0 := h4845c.1
                                          have p4845_1 := h4845c.2.1
                                          have p4845_2 := h4845c.2.2.1
                                          have p4845_3 := h4845c.2.2.2
                                          linarith only [hlam, p4845_0]
                                  · linarith only [h4818, h4840, hlam]
                                · linarith only [h4814, h4839, hlam]
                              · linarith only [h4838, hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h3607, h4789, h4810, h4817, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4823_1, u4ehi3]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h4810, hlam, p4823_1]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              rcases p4823_3 (m.d 0 3) (by simp) with h4877 | h4877
                              · linarith only [h2760, h4877, hlam]
                              · linarith only [h4790, h4877, hlam]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              rcases p4823_3 (m.d 0 3) (by simp) with h4880 | h4880
                              · linarith only [h2760, h4880, hlam]
                              · linarith only [h4791, h4880, hlam]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h3607, h4789, h4817, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4823_1, u4ehi3]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h2760, hc01, hc23, hlam, hphi, ht12, p4823_1]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              rcases p4823_3 (m.d 0 3) (by simp) with h4886 | h4886
                              · linarith only [h3607, h4886, hlam]
                              · linarith only [h4790, h4886, hlam]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              rcases p4823_3 (m.d 0 3) (by simp) with h4889 | h4889
                              · linarith only [h3607, h4889, hlam]
                              · linarith only [h4791, h4889, hlam]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h4790, hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h4813, hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h4817, hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h4821, hlam, p4823_1]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h4791, hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h4814, hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h4818, hlam, p4823_0]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [h4791, hc03, hlam, hphi, ht0b, ht45, ht5b, p4823_1, u4ehi3]
                            · have p4823_0 := h4823c.1
                              have p4823_1 := h4823c.2.1
                              have p4823_2 := h4823c.2.2.1
                              have p4823_3 := h4823c.2.2.2
                              linarith only [hlam, p4823_0]
                      · linarith only [h2760, h4791, h4810, h4818, hlam]
                    · linarith only [h0, h4810, h4817, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h2760, h4791, h4814, hlam]
              · linarith only [h2760, h3607, h4789, h4790, h4813, hlam]
            · linarith only [h0, h2760, h3607, h4789, h4812, hc01, hc13, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4907 | h4907
        · linarith only [h3607, h4789, h4791, h4907, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4909 | h4909
          · linarith only [h3607, h4789, h4909, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4911 | h4911
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4912 | h4912
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4913 | h4913
                · linarith only [h4790, h4791, h4913, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4915 | h4915
                  · linarith only [h4907, h4909, h4911, h4913, h4915, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4917 | h4917
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4918 | h4918
                      · linarith only [h0, h4909, h4913, h4918, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h3607, h4789, h4917, h4918, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h4789, h4909, h4917, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · linarith only [h3404, h4790, h4909, h4911, h4912, hlam]
            · linarith only [h0, h4789, h4911, hlam]
    · linarith only [h3607, h4789, h4790, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4925 | h4925
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4926 | h4926
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4927 | h4927
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4928 | h4928
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4929 | h4929
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4930 | h4930
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4931 | h4931
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4932 | h4932
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4933 | h4933
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4934 | h4934
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4935 | h4935
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4936 | h4936
                          · linarith only [h3607, h4925, h4928, h4936, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h4789, h4927, h4928, h4933, h4936, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h4789, h4927, h4935, hlam]
                      · linarith only [h3607, h4926, h4934, hlam]
                    · linarith only [h3607, h4925, h4933, hlam]
                  · linarith only [h3404, h4789, h4927, h4932, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h2760, h3607, h4926, h4928, h4931, hc01, hc12, hlam, hphi]
              · linarith only [h3607, h4925, h4928, h4930, hlam]
            · linarith only [h3607, h4925, h4928, h4929, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4946 | h4946
            · linarith only [h0, h4789, h4928, h4946, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4948 | h4948
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4949 | h4949
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4950 | h4950
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4951 | h4951
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4952 | h4952
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h4953 | h4953
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h4954 | h4954
                          · rcases h3bigk with h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c | h4955c
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h2760, hlam, p4955_1]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h3607, hlam, p4955_1]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4954, hc03, hlam, hphi, ht0b, ht45, ht5b, p4955_1, u4ehi4]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              rcases p4955_3 (m.d 0 3) (by simp) with h4960 | h4960
                              · rcases p4955_3 (m.d 1 3) (by simp) with h4961 | h4961
                                · rcases p4955_3 (m.d 2 3) (by simp) with h4962 | h4962
                                  · rcases p4955_3 (m.d 3 4) (by simp) with h4963 | h4963
                                    · linarith only [h4925, h4963, hlam]
                                    · linarith only [h4954, h4963, hlam]
                                  · linarith only [h4952, h4962, hlam]
                                · linarith only [h4949, h4961, hlam]
                              · linarith only [h4960, hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4925, h4928, h4954, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4955_1, u4ehi4]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4928, hlam, p4955_1]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4928, h4954, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4955_1, u4ehi4]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              rcases p4955_3 (m.d 0 3) (by simp) with h4973 | h4973
                              · linarith only [h2760, h4973, hlam]
                              · linarith only [h4926, h4973, hlam]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4925, h4954, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4955_1, u4ehi4]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h2760, h4925, h4954, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4955_1, u4ehi4]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4954, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4955_1, u4ehi4]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              rcases p4955_3 (m.d 0 3) (by simp) with h4980 | h4980
                              · linarith only [h3607, h4980, hlam]
                              · linarith only [h4926, h4980, hlam]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4925, hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4948, hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4951, hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4925, h4954, hc03, hlam, hphi, ht0b, ht45, ht5b, p4955_1, u4ehi4]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4926, hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4949, hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4952, hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [h4954, hlam, p4955_0]
                            · have p4955_0 := h4955c.1
                              have p4955_1 := h4955c.2.1
                              have p4955_2 := h4955c.2.2.1
                              have p4955_3 := h4955c.2.2.2
                              linarith only [hlam, p4955_0]
                          · rcases h3bigk with h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c | h4993c
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h2760, hlam, p4993_1]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h3607, hlam, p4993_1]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              rcases p4993_3 (m.d 0 3) (by simp) with h4997 | h4997
                              · rcases p4993_3 (m.d 1 3) (by simp) with h4998 | h4998
                                · rcases p4993_3 (m.d 2 3) (by simp) with h4999 | h4999
                                  · rcases p4993_3 (m.d 3 4) (by simp) with h5000 | h5000
                                    · linarith only [h5000, hlam, p4993_0]
                                    · rcases p4993_3 (m.d 3 5) (by simp) with h5002 | h5002
                                      · linarith only [h4926, h5002, hlam]
                                      · linarith only [h4954, h5002, hlam]
                                  · linarith only [h4951, h4999, hlam]
                                · linarith only [h4948, h4998, hlam]
                              · linarith only [h4997, hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              rcases p4993_3 (m.d 0 3) (by simp) with h5008 | h5008
                              · rcases p4993_3 (m.d 1 3) (by simp) with h5009 | h5009
                                · rcases p4993_3 (m.d 2 3) (by simp) with h5010 | h5010
                                  · rcases p4993_3 (m.d 3 4) (by simp) with h5011 | h5011
                                    · linarith only [h4925, h5011, hlam]
                                    · rcases p4993_3 (m.d 3 5) (by simp) with h5013 | h5013
                                      · linarith only [h5013, hlam, p4993_0]
                                      · rcases h4bigk with h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h3404, hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4789, hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          rcases p5015_3 (m.d 0 4) (by simp) with h5019 | h5019
                                          · rcases p5015_3 (m.d 1 4) (by simp) with h5020 | h5020
                                            · rcases p5015_3 (m.d 2 4) (by simp) with h5021 | h5021
                                              · rcases p5015_3 (m.d 3 4) (by simp) with h5022 | h5022
                                                · linarith only [h4925, h5022, hlam]
                                                · rcases p5015_3 (m.d 4 5) (by simp) with h5024 | h5024
                                                  · linarith only [h4927, h5024, hlam]
                                                  · linarith only [h4954, h5024, hlam]
                                              · linarith only [h4951, h5021, hlam]
                                            · linarith only [h4948, h5020, hlam]
                                          · linarith only [h4925, h5019, hlam]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h2760, h4925, h4928, h4954, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5015_1, u4ehi3]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4927, h4946, h4951, h4954, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5015_1, u4ehi3]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4946, hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          rcases p5015_3 (m.d 0 4) (by simp) with h5034 | h5034
                                          · linarith only [h3404, h5034, hlam]
                                          · linarith only [h4925, h5034, hlam]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4946, h4951, h4954, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5015_1, u4ehi3]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4927, h4951, h4954, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5015_1, u4ehi3]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h3404, h4951, hc01, hc23, hlam, hphi, ht12, p5015_1]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          rcases p5015_3 (m.d 0 4) (by simp) with h5041 | h5041
                                          · linarith only [h4789, h5041, hlam]
                                          · linarith only [h4925, h5041, hlam]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4951, h4954, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5015_1, u4ehi3]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4925, hlam, p5015_1]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4948, hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4951, hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4954, hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4927, hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4950, hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4953, hlam, p5015_0]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [h4927, hc04, hlam, hphi, ht0b, ht45, ht5b, p5015_1, u4ehi3]
                                        · have p5015_0 := h5015c.1
                                          have p5015_1 := h5015c.2.1
                                          have p5015_2 := h5015c.2.2.1
                                          have p5015_3 := h5015c.2.2.2
                                          linarith only [hlam, p5015_0]
                                  · linarith only [h4952, h5010, hlam]
                                · linarith only [h4949, h5009, hlam]
                              · linarith only [h5008, hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h4925, h4928, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4993_1, u4ehi3]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h4928, hlam, p4993_1]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              rcases p4993_3 (m.d 0 3) (by simp) with h5061 | h5061
                              · linarith only [h2760, h5061, hlam]
                              · linarith only [h4925, h5061, hlam]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              rcases p4993_3 (m.d 0 3) (by simp) with h5064 | h5064
                              · linarith only [h2760, h5064, hlam]
                              · linarith only [h4926, h5064, hlam]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h4925, h4927, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4993_1, u4ehi4]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h2760, hc01, hc23, hlam, hphi, ht12, p4993_1]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              rcases p4993_3 (m.d 0 3) (by simp) with h5070 | h5070
                              · linarith only [h3607, h5070, hlam]
                              · linarith only [h4925, h5070, hlam]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              rcases p4993_3 (m.d 0 3) (by simp) with h5073 | h5073
                              · linarith only [h3607, h5073, hlam]
                              · linarith only [h4926, h5073, hlam]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h4925, hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h4948, hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h4951, hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h4954, hlam, p4993_1]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h4926, hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h4949, hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h4952, hlam, p4993_0]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [h4926, hc03, hlam, hphi, ht0b, ht45, ht5b, p4993_1, u4ehi3]
                            · have p4993_0 := h4993c.1
                              have p4993_1 := h4993c.2.1
                              have p4993_2 := h4993c.2.2.1
                              have p4993_3 := h4993c.2.2.2
                              linarith only [hlam, p4993_0]
                        · linarith only [h3404, h4927, h4946, h4953, hlam]
                      · linarith only [h2760, h4926, h4928, h4952, hlam]
                    · linarith only [h2760, h4925, h4928, h4951, hlam]
                  · linarith only [h3404, h4927, h4950, hlam]
                · linarith only [h2760, h4926, h4949, hlam]
              · linarith only [h2760, h4925, h4948, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5092 | h5092
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5093 | h5093
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5094 | h5094
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5095 | h5095
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5096 | h5096
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5097 | h5097
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5098 | h5098
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5099 | h5099
                        · linarith only [h4925, h4927, h5092, h5097, h5099, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h4789, h5094, h5096, h5099, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h2760, h3607, h4926, h5092, h5098, hc01, hc12, hlam, hphi]
                    · linarith only [h3607, h4925, h5097, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5104 | h5104
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5105 | h5105
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5106 | h5106
                        · linarith only [h5093, h5096, h5106, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5108 | h5108
                          · linarith only [h4789, h4925, h5093, h5096, h5108, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · rcases h3bigk with h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c | h5110c
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [hlam, p5110_0]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h2760, hlam, p5110_1]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h3607, hlam, p5110_1]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h3607, h5092, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5110_1, u4ehi3]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h3607, h5092, h5108, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5110_1, u4ehi3]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h4925, h5092, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5110_1, u4ehi3]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [hlam, p5110_0]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h0, h3607, h5092, hc01, hc12, hlam, hphi, p5110_1]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              rcases p5110_3 (m.d 0 3) (by simp) with h5119 | h5119
                              · linarith only [h2760, h5119, hlam]
                              · linarith only [h4925, h5119, hlam]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              rcases p5110_3 (m.d 0 3) (by simp) with h5122 | h5122
                              · linarith only [h2760, h5122, hlam]
                              · linarith only [h4926, h5122, hlam]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h4926, h5108, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5110_1, u4ehi3]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h5092, hlam, p5110_0]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [hlam, p5110_0]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h5092, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5110_1, u4ehi3]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h5092, h5108, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5110_1, u4ehi3]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h4925, hlam, p5110_0]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h5094, hlam, p5110_0]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h5104, hlam, p5110_0]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [hlam, p5110_0]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h5108, hlam, p5110_1]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h4926, hlam, p5110_0]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h5095, hlam, p5110_0]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h5105, hlam, p5110_0]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [h4926, hc03, hlam, hphi, ht0b, ht45, ht5b, p5110_1, u4ehi3]
                            · have p5110_0 := h5110c.1
                              have p5110_1 := h5110c.2.1
                              have p5110_2 := h5110c.2.2.1
                              have p5110_3 := h5110c.2.2.2
                              linarith only [hlam, p5110_0]
                      · linarith only [h3607, h4926, h5105, hlam]
                    · linarith only [h0, h3404, h3607, h4925, h5096, h5104, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h2760, h3607, h4926, h5095, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h2760, h4925, h4927, h5094, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h3607, h5092, h5093, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5145 | h5145
            · linarith only [h0, h4789, h5092, h5145, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5147 | h5147
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5148 | h5148
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5149 | h5149
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5150 | h5150
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5151 | h5151
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5152 | h5152
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5153 | h5153
                          · linarith only [h4925, h4927, h5153, hlam]
                          · rcases h3bigk with h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c | h5155c
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h2760, hlam, p5155_1]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h3607, hlam, p5155_1]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              rcases p5155_3 (m.d 0 3) (by simp) with h5159 | h5159
                              · rcases p5155_3 (m.d 1 3) (by simp) with h5160 | h5160
                                · rcases p5155_3 (m.d 2 3) (by simp) with h5161 | h5161
                                  · rcases p5155_3 (m.d 3 4) (by simp) with h5162 | h5162
                                    · linarith only [h5162, hlam, p5155_0]
                                    · rcases p5155_3 (m.d 3 5) (by simp) with h5164 | h5164
                                      · linarith only [h4926, h5164, hlam]
                                      · linarith only [h5153, h5164, hlam]
                                  · linarith only [h5150, h5161, hlam]
                                · linarith only [h5147, h5160, hlam]
                              · linarith only [h5159, hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              rcases p5155_3 (m.d 0 3) (by simp) with h5170 | h5170
                              · rcases p5155_3 (m.d 1 3) (by simp) with h5171 | h5171
                                · rcases p5155_3 (m.d 2 3) (by simp) with h5172 | h5172
                                  · rcases p5155_3 (m.d 3 4) (by simp) with h5173 | h5173
                                    · linarith only [h4925, h5173, hlam]
                                    · rcases p5155_3 (m.d 3 5) (by simp) with h5175 | h5175
                                      · linarith only [h5175, hlam, p5155_0]
                                      · rcases h4bigk with h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c | h5177c
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h3404, hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h4789, hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h4927, h5149, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5177_1, u4ehi3]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h4927, hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          rcases p5177_3 (m.d 0 4) (by simp) with h5183 | h5183
                                          · linarith only [h3404, h5183, hlam]
                                          · rcases p5177_3 (m.d 1 4) (by simp) with h5185 | h5185
                                            · rcases p5177_3 (m.d 2 4) (by simp) with h5186 | h5186
                                              · rcases p5177_3 (m.d 3 4) (by simp) with h5187 | h5187
                                                · linarith only [h5147, h5187, hlam]
                                                · rcases p5177_3 (m.d 4 5) (by simp) with h5189 | h5189
                                                  · linarith only [h5149, h5189, hlam]
                                                  · linarith only [h4927, h5189, hlam]
                                              · linarith only [h4789, h5186, hlam]
                                            · linarith only [h3404, h5185, hlam]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h5145, hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          rcases p5177_3 (m.d 0 4) (by simp) with h5196 | h5196
                                          · linarith only [h3404, h5196, hlam]
                                          · linarith only [h4925, h5196, hlam]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h4927, h5145, h5150, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5177_1, u4ehi0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          rcases p5177_3 (m.d 0 4) (by simp) with h5200 | h5200
                                          · linarith only [h4789, h5200, hlam]
                                          · rcases p5177_3 (m.d 1 4) (by simp) with h5202 | h5202
                                            · linarith only [h5145, h5202, hlam]
                                            · linarith only [h3404, h5202, hlam]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h3404, h5150, hc01, hc23, hlam, hphi, ht12, p5177_1]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          rcases p5177_3 (m.d 0 4) (by simp) with h5207 | h5207
                                          · linarith only [h4789, h5207, hlam]
                                          · linarith only [h4925, h5207, hlam]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h4925, h4927, h5150, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5177_1, u4ehi3]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h4925, hlam, p5177_1]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h5147, hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h5150, hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h5153, hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h4925, h5149, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5177_1, u4ehi3]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h5149, hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h5152, hlam, p5177_0]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [h5145, h5149, h5150, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5177_1, u4ehi3]
                                        · have p5177_0 := h5177c.1
                                          have p5177_1 := h5177c.2.1
                                          have p5177_2 := h5177c.2.2.1
                                          have p5177_3 := h5177c.2.2.2
                                          linarith only [hlam, p5177_0]
                                  · linarith only [h5151, h5172, hlam]
                                · linarith only [h5148, h5171, hlam]
                              · linarith only [h5170, hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h4925, h5092, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5155_1, u4ehi3]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h5092, hlam, p5155_1]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              rcases p5155_3 (m.d 0 3) (by simp) with h5227 | h5227
                              · linarith only [h2760, h5227, hlam]
                              · linarith only [h4925, h5227, hlam]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              rcases p5155_3 (m.d 0 3) (by simp) with h5230 | h5230
                              · linarith only [h2760, h5230, hlam]
                              · linarith only [h4926, h5230, hlam]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h4926, h5153, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5155_1, u4ehi3]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h2760, hc01, hc23, hlam, hphi, ht12, p5155_1]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              rcases p5155_3 (m.d 0 3) (by simp) with h5236 | h5236
                              · linarith only [h3607, h5236, hlam]
                              · linarith only [h4925, h5236, hlam]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              rcases p5155_3 (m.d 0 3) (by simp) with h5239 | h5239
                              · linarith only [h3607, h5239, hlam]
                              · linarith only [h4926, h5239, hlam]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h4925, hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h5147, hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h5150, hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h5153, hlam, p5155_1]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h4926, hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h5148, hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h5151, hlam, p5155_0]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [h4926, hc03, hlam, hphi, ht0b, ht45, ht5b, p5155_1, u4ehi3]
                            · have p5155_0 := h5155c.1
                              have p5155_1 := h5155c.2.1
                              have p5155_2 := h5155c.2.2.1
                              have p5155_3 := h5155c.2.2.2
                              linarith only [hlam, p5155_0]
                        · linarith only [h5145, h5149, h5152, hlam]
                      · linarith only [h4926, h4927, h5145, h5149, h5150, h5151, hlam]
                    · linarith only [h2760, h4925, h5092, h5150, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5255 | h5255
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5256 | h5256
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5257 | h5257
                        · linarith only [h0, h5145, h5149, h5255, h5257, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h5145, h5257, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h2760, h4926, h5092, h5256, hlam]
                    · linarith only [h2760, h4925, h5092, h5255, hlam]
                · linarith only [h2760, h4926, h5148, hlam]
              · linarith only [h2760, h4925, h5147, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5264 | h5264
        · linarith only [h4925, h4926, h5264, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5266 | h5266
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5267 | h5267
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5268 | h5268
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5269 | h5269
                · linarith only [h4925, h4926, h5269, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5271 | h5271
                  · linarith only [h5264, h5268, h5269, h5271, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5273 | h5273
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5274 | h5274
                      · linarith only [h2760, h5269, h5274, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5276 | h5276
                        · linarith only [h3404, h5271, h5276, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5278 | h5278
                          · linarith only [h0, h4789, h4925, h5267, h5271, h5278, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · linarith only [h3607, h4925, h5266, h5269, h5278, hc45, hlam, hphi, u4ehi3]
                    · linarith only [h3607, h4925, h5273, hlam]
              · linarith only [h3607, h4925, h5266, h5268, hlam]
            · linarith only [h3607, h4925, h5266, h5267, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5284 | h5284
            · linarith only [h4789, h5266, h5284, hc02, hc23, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5286 | h5286
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5287 | h5287
                · linarith only [h4925, h4926, h5287, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5289 | h5289
                  · linarith only [h4925, h5264, h5286, h5287, h5289, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5291 | h5291
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5292 | h5292
                      · linarith only [h2760, h5287, h5292, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h5266, h5292, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h4925, h5266, h5291, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
              · linarith only [h4925, h4926, h5286, hc13, hc35, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5297 | h5297
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5298 | h5298
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5299 | h5299
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5300 | h5300
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5301 | h5301
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5302 | h5302
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5303 | h5303
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5304 | h5304
                    · linarith only [h4925, h5297, h5299, h5304, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h3607, h5299, h5301, h5304, hc01, hc12, hlam, hphi]
                  · linarith only [h3404, h4789, h5298, h5303, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h4925, h5297, h5298, h5301, h5302, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5309 | h5309
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5310 | h5310
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5311 | h5311
                    · linarith only [h2760, h5301, h5311, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5313 | h5313
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5314 | h5314
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5315 | h5315
                          · rcases h3bigk with h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c | h5316c
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h2760, hlam, p5316_1]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h3607, hlam, p5316_1]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h4925, hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h3607, h5299, h5301, h5315, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5316_1, u4ehi4]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5301, hc03, hc34, hlam, hphi, p5316_1]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5301, hc23, hc34, hlam, hphi, p5316_1]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5301, hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5301, h5315, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5316_1, u4ehi4]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5297, h5315, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5316_1, u4ehi4]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5299, hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5311, hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5299, h5301, h5315, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5316_1, u4ehi4]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5297, h5315, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5316_1, u4ehi4]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h2760, hc01, hc34, hlam, hphi, ht12, ht23, p5316_1]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h3607, h5297, h5315, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5316_1, u4ehi4]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              rcases p5316_3 (m.d 0 3) (by simp) with h5336 | h5336
                              · linarith only [h4925, h5336, hlam]
                              · linarith only [h5297, h5336, hlam]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5297, hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5309, hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5313, hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [h5315, hlam, p5316_0]
                            · have p5316_0 := h5316c.1
                              have p5316_1 := h5316c.2.1
                              have p5316_2 := h5316c.2.2.1
                              have p5316_3 := h5316c.2.2.2
                              linarith only [hlam, p5316_0]
                          · linarith only [h4789, h4925, h5297, h5298, h5315, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h4789, h5298, h5314, hlam]
                      · linarith only [h3607, h5297, h5313, hlam]
                  · linarith only [h4789, h5298, h5300, h5310, hlam]
                · linarith only [h3607, h5297, h5299, h5309, hlam]
            · linarith only [h0, h3607, h5299, h5300, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5350 | h5350
            · linarith only [h0, h4789, h5299, h5350, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5352 | h5352
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5353 | h5353
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5354 | h5354
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5355 | h5355
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5356 | h5356
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5357 | h5357
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5358 | h5358
                          · linarith only [h4925, h5297, h5299, h5352, h5358, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h4925, h5298, h5358, hlam]
                        · linarith only [h4925, h5297, h5298, h5350, h5357, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h4925, h5297, h5299, h5352, h5356, hlam]
                    · linarith only [h5299, h5352, h5355, hlam]
                  · linarith only [h4925, h5297, h5298, h5299, h5352, h5354, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h4925, h5297, h5352, h5353, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5366 | h5366
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5367 | h5367
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5368 | h5368
                    · linarith only [h0, h5299, h5352, h5368, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h5299, h5368, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3404, h5298, h5367, hlam]
                · linarith only [h2760, h5297, h5366, hlam]
        · linarith only [h4925, h5297, h5298, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5374 | h5374
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5375 | h5375
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5376 | h5376
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5377 | h5377
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5378 | h5378
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5379 | h5379
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5380 | h5380
                    · linarith only [h0, h3607, h4925, h5375, h5380, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h3607, h5375, h5377, h5380, hc01, hc12, hlam, hphi]
                  · linarith only [h4789, h5374, h5376, h5379, hlam]
                · linarith only [h0, h3607, h4925, h5377, h5378, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5385 | h5385
                · linarith only [h0, h3607, h5297, h5377, h5385, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5387 | h5387
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5388 | h5388
                    · linarith only [h2760, h5377, h5388, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5390 | h5390
                      · linarith only [h5375, h5385, h5390, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5392 | h5392
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5393 | h5393
                          · rcases h3bigk with h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c | h5394c
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h2760, hlam, p5394_1]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h3607, hlam, p5394_1]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h4925, hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h5297, hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h0, h3607, h5385, h5393, hc01, hc34, hlam, hphi, ht12, ht23, p5394_1]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h0, h3607, h5385, h5393, hc01, hc34, hlam, hphi, ht12, ht23, p5394_1]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h5377, hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h5385, hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h0, h3607, h5375, hc01, hc12, hlam, hphi, p5394_1]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h5375, hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h5388, hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h5390, hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              rcases p5394_3 (m.d 0 3) (by simp) with h5410 | h5410
                              · linarith only [h5410, hlam, p5394_0]
                              · rcases p5394_3 (m.d 1 3) (by simp) with h5412 | h5412
                                · linarith only [h5377, h5412, hlam]
                                · linarith only [h2760, h5412, hlam]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h2760, hc01, hc34, hlam, hphi, ht12, ht23, p5394_1]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h0, h3607, hc01, hc34, hlam, hphi, ht12, ht23, p5394_1]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h0, h3607, h5297, hc01, hc34, hlam, hphi, ht12, ht23, p5394_1]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              rcases p5394_3 (m.d 0 3) (by simp) with h5419 | h5419
                              · linarith only [h5419, hlam, p5394_0]
                              · rcases p5394_3 (m.d 1 3) (by simp) with h5421 | h5421
                                · linarith only [h5385, h5421, hlam]
                                · linarith only [h2760, h5421, hlam]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h0, h3607, h5375, hc01, hc35, hlam, hphi, ht12, ht23, p5394_1]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h0, h3607, hc01, hc35, hlam, hphi, ht12, ht23, p5394_1]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [h5393, hlam, p5394_0]
                            · have p5394_0 := h5394c.1
                              have p5394_1 := h5394c.2.1
                              have p5394_2 := h5394c.2.2.1
                              have p5394_3 := h5394c.2.2.2
                              linarith only [hlam, p5394_0]
                          · linarith only [h0, h3607, h4789, h4925, h5374, h5376, h5393, hc01, hc14, hlam, hphi]
                        · linarith only [h4789, h5374, h5392, hlam]
                  · linarith only [h4789, h5374, h5376, h5387, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
            · linarith only [h0, h3607, h5375, h5376, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5432 | h5432
            · linarith only [h0, h4789, h5375, h5432, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5434 | h5434
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5435 | h5435
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5436 | h5436
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5437 | h5437
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5438 | h5438
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5439 | h5439
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5440 | h5440
                          · rcases h3bigk with h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c | h5441c
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [hlam, p5441_0]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h2760, hlam, p5441_1]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h3607, hlam, p5441_1]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h4925, hlam, p5441_0]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h5297, hlam, p5441_0]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              rcases p5441_3 (m.d 0 3) (by simp) with h5447 | h5447
                              · linarith only [h2760, h5447, hlam]
                              · rcases p5441_3 (m.d 1 3) (by simp) with h5449 | h5449
                                · rcases p5441_3 (m.d 2 3) (by simp) with h5450 | h5450
                                  · rcases p5441_3 (m.d 3 4) (by simp) with h5451 | h5451
                                    · linarith only [h5434, h5451, hlam]
                                    · linarith only [h4925, h5451, hlam]
                                  · linarith only [h3607, h5450, hlam]
                                · linarith only [h2760, h5449, hlam]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [hlam, p5441_0]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h5375, hlam, p5441_1]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h4925, h5374, h5375, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5441_1, u4ehi4]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h0, h3607, h5297, h5375, hc01, hc23, hlam, hphi, ht12, p5441_1]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              rcases p5441_3 (m.d 0 3) (by simp) with h5460 | h5460
                              · linarith only [h3607, h5460, hlam]
                              · rcases p5441_3 (m.d 1 3) (by simp) with h5462 | h5462
                                · linarith only [h5375, h5462, hlam]
                                · linarith only [h2760, h5462, hlam]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h2760, hc01, hc23, hlam, hphi, ht12, p5441_1]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [hlam, p5441_0]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h4925, h5374, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5441_1, u4ehi4]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h0, h3607, h5297, hc01, hc23, hlam, hphi, ht12, p5441_1]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h0, h3607, h5434, hc01, hc13, hlam, hphi, p5441_1]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h5434, hlam, p5441_0]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h5437, hlam, p5441_0]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [hlam, p5441_0]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h0, h3607, h5297, h5375, h5434, hc01, hc23, hlam, hphi, ht12, p5441_1]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h0, h3607, h5375, h5435, hc01, hc23, hlam, hphi, ht12, p5441_1]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h5435, hlam, p5441_0]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h5438, hlam, p5441_0]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [h5440, hlam, p5441_0]
                            · have p5441_0 := h5441c.1
                              have p5441_1 := h5441c.2.1
                              have p5441_2 := h5441c.2.2.1
                              have p5441_3 := h5441c.2.2.2
                              linarith only [hlam, p5441_0]
                          · linarith only [h0, h3404, h3607, h4925, h5374, h5440, hc01, hc14, hlam, hphi]
                        · linarith only [h4925, h5374, h5375, h5432, h5434, h5439, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                      · linarith only [h5375, h5435, h5438, hlam]
                    · linarith only [h5375, h5434, h5437, hlam]
                  · linarith only [h4925, h5374, h5375, h5434, h5436, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h4925, h5374, h5434, h5435, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5485 | h5485
                · linarith only [h0, h3607, h5297, h5434, h5485, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5487 | h5487
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5488 | h5488
                    · linarith only [h2760, h5434, h5488, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h5375, h5488, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3404, h5374, h5487, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5492 | h5492
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5493 | h5493
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5494 | h5494
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5495 | h5495
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5496 | h5496
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5497 | h5497
                    · linarith only [h0, h3607, h4925, h5492, h5497, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h3607, h5492, h5494, h5497, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5500 | h5500
                    · linarith only [h0, h3607, h4925, h5492, h5500, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h3607, h5494, h5496, h5500, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h3607, h4925, h5494, h5495, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5504 | h5504
                · linarith only [h0, h3607, h5297, h5494, h5504, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5506 | h5506
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5507 | h5507
                    · linarith only [h5374, h5494, h5506, h5507, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5509 | h5509
                      · linarith only [h5492, h5504, h5509, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5511 | h5511
                        · linarith only [h5374, h5493, h5511, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · linarith only [h0, h4789, h5494, h5506, h5511, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5514 | h5514
                    · linarith only [h0, h3607, h4925, h5492, h5504, h5514, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5516 | h5516
                      · linarith only [h0, h3607, h5297, h5492, h5494, h5506, h5516, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5518 | h5518
                        · linarith only [h2760, h5494, h5506, h5518, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5520 | h5520
                          · linarith only [h0, h3607, h5492, h5494, h5506, h5520, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h3607, h5492, h5494, h5520, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h3607, h5492, h5493, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5524 | h5524
            · linarith only [h0, h4789, h5492, h5524, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5526 | h5526
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5527 | h5527
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5528 | h5528
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5529 | h5529
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5530 | h5530
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5531 | h5531
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5532 | h5532
                          · linarith only [h5374, h5492, h5526, h5532, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h3607, h4925, h5528, h5532, hc01, hc14, hlam, hphi]
                        · linarith only [h5524, h5528, h5531, hlam]
                      · linarith only [h5492, h5527, h5530, hlam]
                    · linarith only [h0, h3607, h5297, h5492, h5527, h5529, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5538 | h5538
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5539 | h5539
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5540 | h5540
                        · linarith only [h0, h3607, h4925, h5526, h5528, h5540, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h5524, h5540, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h5492, h5527, h5539, hlam]
                    · linarith only [h0, h3607, h5297, h5492, h5526, h5527, h5538, hc01, hc14, hlam, hphi]
                · linarith only [h0, h3607, h4925, h5526, h5527, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h5546 | h5546
                · linarith only [h0, h3607, h5297, h5526, h5546, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5548 | h5548
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5549 | h5549
                    · linarith only [h5374, h5526, h5548, h5549, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · linarith only [h0, h5492, h5549, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5552 | h5552
                    · linarith only [h0, h5492, h5526, h5552, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h5492, h5552, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_13_24_L_I_M_IR_s1_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2760 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3404 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3607 | h3607
  · exact r1l7_13_24_L_I_M_IR_s1_x1_x1_x0 m hb3 hb4 hg0 h2760 h3404 h3607
  · exact r1l7_13_24_L_I_M_IR_s1_x1_x1_x1 m hb3 hb4 hg0 h2760 h3404 h3607

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_13_24_L_I_M_IR_s1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2760 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h3404 | h3404
  · exact r1l7_13_24_L_I_M_IR_s1_x1_x0 m hb3 hb4 hg0 h2760 h3404
  · exact r1l7_13_24_L_I_M_IR_s1_x1_x1 m hb3 hb4 hg0 h2760 h3404

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_13_24_L_I_M_IR_s1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h2760 | h2760
  · exact r1l7_13_24_L_I_M_IR_s1_x0 m hb3 hb4 hg0 h2760
  · exact r1l7_13_24_L_I_M_IR_s1_x1 m hb3 hb4 hg0 h2760

set_option maxHeartbeats 11110000 in
set_option maxHeartbeats 11110000 in
theorem r1l7_13_24_L_I_M_IR (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_13_24_L_I_M_IR_s0 m hb3 hb4 h0
  · exact r1l7_13_24_L_I_M_IR_s1 m hb3 hb4 h0

end R2N4
