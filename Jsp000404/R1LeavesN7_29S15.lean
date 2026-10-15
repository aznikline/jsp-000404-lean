import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_29S12
import Jsp000404.R1LeavesN7_29S13
import Jsp000404.R1LeavesN7_29S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10528000 in
set_option maxHeartbeats 10528000 in
theorem r1l7_21_15_M_LI_L_I_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3078 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3604 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3964 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4232 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h4809 | h4809
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4810 | h4810
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4811 | h4811
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4812 | h4812
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4813 | h4813
          · linarith only [h4232, h4809, h4813, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4815 | h4815
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4816 | h4816
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4817 | h4817
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4818 | h4818
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4819 | h4819
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4820 | h4820
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4821 | h4821
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4822 | h4822
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4823 | h4823
                            · rcases h1bigk with h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c | h4824c
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h0, hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h3078, hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h3604, hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h3964, hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h4813, hc01, hc23, hlam, hphi, ht12, p4824_1]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h4813, hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h3604, h4813, hc01, hc23, hlam, hphi, ht12, p4824_1]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h3964, h4813, hc01, hc23, hlam, hphi, ht12, p4824_1]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [hc01, hlam, hphi, p4824_1, u1elo2]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h4815, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4824_1, u1elo2]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h3964, h4819, hc01, hlam, hphi, p4824_1, u1elo2]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4824_1, u1elo2]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h4815, hc01, hlam, hphi, p4824_1, u1elo1]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h4815, hlam, p4824_1]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h4817, hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h3964, h4813, h4815, hc01, hc23, hlam, hphi, ht12, p4824_1]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [hc01, hlam, hphi, p4824_1, u1elo4]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h4816, hlam, p4824_1]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h4818, hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [h4819, hlam, p4824_0]
                              · have p4824_0 := h4824c.1
                                have p4824_1 := h4824c.2.1
                                have p4824_2 := h4824c.2.2.1
                                have p4824_3 := h4824c.2.2.2
                                linarith only [hlam, p4824_0]
                            · linarith only [h4813, h4815, h4822, h4823, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4851 | h4851
                            · linarith only [h4820, h4822, h4851, hlam]
                            · rcases h1bigk with h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c | h4853c
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h0, hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h3078, hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h3604, hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h3964, hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h4813, hc01, hc23, hlam, hphi, ht12, p4853_1]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h4813, hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h3604, h4813, hc01, hc23, hlam, hphi, ht12, p4853_1]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h3964, h4813, hc01, hc23, hlam, hphi, ht12, p4853_1]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [hc01, hlam, hphi, p4853_1, u1elo2]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p4853_1, u1elo2]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h3604, h4812, h4820, h4822, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4853_1, u1elo2]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4853_1, u1elo2]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h4815, hc01, hlam, hphi, p4853_1, u1elo1]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h4815, hlam, p4853_1]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h4817, hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h3964, h4813, h4815, hc01, hc23, hlam, hphi, ht12, p4853_1]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [hc01, hlam, hphi, p4853_1, u1elo4]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h4816, hlam, p4853_1]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h4818, hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [h4819, hlam, p4853_0]
                              · have p4853_0 := h4853c.1
                                have p4853_1 := h4853c.2.1
                                have p4853_2 := h4853c.2.2.1
                                have p4853_3 := h4853c.2.2.2
                                linarith only [hlam, p4853_0]
                        · linarith only [h0, h4813, h4821, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h3964, h4813, h4815, h4819, h4820, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h3604, h4812, h4819, hlam]
                  · linarith only [h0, h3078, h4809, h4811, h4813, h4818, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h3078, h4810, h4817, hlam]
              · linarith only [h0, h4809, h4816, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4885 | h4885
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4886 | h4886
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4887 | h4887
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4888 | h4888
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4889 | h4889
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4890 | h4890
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4891 | h4891
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4892 | h4892
                            · rcases h1bigk with h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c | h4893c
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h0, hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h3078, hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h3604, hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h3964, hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h4815, h4886, hc01, hlam, hphi, p4893_1, u1elo2]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h4813, hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h4815, hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h3964, h4815, h4886, hc01, hlam, hphi, p4893_1, u1elo2]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [hc01, hlam, hphi, p4893_1, u1elo2]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h0, h4809, hc25, hlam, hphi, ht01, ht0b, ht5b, p4893_1, u1elo2]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p4893_1, u1elo2]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4893_1, u1elo2]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [hc01, hlam, hphi, p4893_1, u1elo3]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h3964, h4885, hc01, hlam, hphi, p4893_1, u1elo3]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h4886, hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h3964, h4886, hc01, hlam, hphi, p4893_1, u1elo2]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h4885, hc01, hlam, hphi, p4893_1, u1elo1]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h4885, hlam, p4893_1]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h4887, hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [h4888, hlam, p4893_0]
                              · have p4893_0 := h4893c.1
                                have p4893_1 := h4893c.2.1
                                have p4893_2 := h4893c.2.2.1
                                have p4893_3 := h4893c.2.2.2
                                linarith only [hlam, p4893_0]
                            · rcases h1bigk with h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c | h4919c
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h0, hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h3078, hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h3604, hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h3964, hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h4815, h4889, hc01, hc23, hlam, hphi, ht12, p4919_1]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h4813, hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h4815, hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h3964, h4815, h4889, hc01, hc23, hlam, hphi, ht12, p4919_1]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [hc01, hlam, hphi, p4919_1, u1elo2]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h0, h4809, hc25, hlam, hphi, ht01, ht0b, ht5b, p4919_1, u1elo2]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p4919_1, u1elo2]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p4919_1, u1elo2]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [hc01, hlam, hphi, p4919_1, u1elo3]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h3964, h4885, hc01, hlam, hphi, p4919_1, u1elo3]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h4886, hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h3964, h4886, hc01, hlam, hphi, p4919_1, u1elo2]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h4885, hc01, hlam, hphi, p4919_1, u1elo1]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h4885, hlam, p4919_1]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h4887, hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [h4888, hlam, p4919_0]
                              · have p4919_0 := h4919c.1
                                have p4919_1 := h4919c.2.1
                                have p4919_2 := h4919c.2.2.1
                                have p4919_3 := h4919c.2.2.2
                                linarith only [hlam, p4919_0]
                          · linarith only [h0, h4815, h4891, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h4232, h4809, h4811, h4890, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h3964, h4813, h4885, h4889, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h3604, h4809, h4812, h4888, hc01, hlam, hphi, u1elo1]
                  · linarith only [h3078, h4811, h4887, hlam]
                · linarith only [h3078, h4810, h4886, hlam]
              · linarith only [h0, h4809, h4885, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4952 | h4952
          · linarith only [h4232, h4809, h4952, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4954 | h4954
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4955 | h4955
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4956 | h4956
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4957 | h4957
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4958 | h4958
                    · linarith only [h3604, h4812, h4952, h4954, h4958, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4960 | h4960
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4961 | h4961
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4962 | h4962
                          · linarith only [h4952, h4954, h4958, h4962, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4964 | h4964
                            · linarith only [h3604, h4809, h4958, h4960, h4962, h4964, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases h1bigk with h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c | h4966c
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [hlam, p4966_0]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h0, hlam, p4966_0]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h3078, hlam, p4966_0]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h3604, hlam, p4966_0]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h3964, hlam, p4966_0]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h4952, hc01, hc23, hlam, hphi, ht12, p4966_1]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [hlam, p4966_0]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h4952, hlam, p4966_0]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h3604, h4952, hc01, hc23, hlam, hphi, ht12, p4966_1]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h3604, h4952, h4958, hc01, hc23, hlam, hphi, ht12, p4966_1]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [hc01, hlam, hphi, p4966_1, u1elo2]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h0, h4809, h4962, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4966_1, u1elo2]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [hlam, p4966_0]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p4966_1, u1elo2]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h3604, h4958, hc01, hlam, hphi, p4966_1, u1elo2]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h4955, h4958, hc01, hlam, hphi, p4966_1, u1elo1]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h4954, hlam, p4966_1]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h4956, hlam, p4966_0]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [hlam, p4966_0]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h4958, hlam, p4966_1]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h4952, h4955, hc01, hc23, hlam, hphi, ht12, p4966_1]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h4955, hlam, p4966_1]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h4957, hlam, p4966_0]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [h3604, h4952, h4955, hc01, hc23, hlam, hphi, ht12, p4966_1]
                              · have p4966_0 := h4966c.1
                                have p4966_1 := h4966c.2.1
                                have p4966_2 := h4966c.2.2.1
                                have p4966_3 := h4966c.2.2.2
                                linarith only [hlam, p4966_0]
                        · linarith only [h0, h4952, h4961, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h3604, h4952, h4955, h4958, h4960, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3078, h3964, h4811, h4952, h4955, h4957, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h3078, h3604, h4810, h4956, hc01, hlam, hphi, u1elo3]
              · linarith only [h0, h4809, h4955, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4997 | h4997
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4998 | h4998
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4999 | h4999
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5000 | h5000
                    · linarith only [h3604, h4812, h4998, h5000, hc01, hlam, hphi, u1elo2]
                    · linarith only [h4954, h4997, h5000, hlam]
                  · linarith only [h3078, h4811, h4999, hlam]
                · linarith only [h0, h3078, h4809, h4810, h4812, h4998, hc01, hlam, hphi, u1elo1]
              · linarith only [h0, h4809, h4997, hlam]
      · linarith only [h4232, h4809, h4811, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5007 | h5007
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5008 | h5008
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5009 | h5009
          · linarith only [h4232, h4809, h5009, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5011 | h5011
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5012 | h5012
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5013 | h5013
                · linarith only [h4232, h4809, h4810, h5013, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · linarith only [h5009, h5011, h5013, hlam]
              · linarith only [h0, h4809, h5012, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5017 | h5017
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5018 | h5018
                · linarith only [h4232, h4809, h4810, h5018, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5020 | h5020
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5021 | h5021
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5022 | h5022
                      · linarith only [h0, h5009, h5018, h5022, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h3964, h5009, h5017, h5022, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h3604, h4809, h5008, h5021, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h3604, h4810, h5007, h5009, h5020, hc01, hlam, hphi, u1elo3]
              · linarith only [h0, h4809, h5017, hlam]
        · linarith only [h4232, h4809, h4810, h5008, hlam]
      · linarith only [h4232, h4809, h5007, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5030 | h5030
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5031 | h5031
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5032 | h5032
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5033 | h5033
          · linarith only [h0, h4232, h5033, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5035 | h5035
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5036 | h5036
              · linarith only [h0, h4809, h5036, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5038 | h5038
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5039 | h5039
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5040 | h5040
                    · linarith only [h5035, h5036, h5040, hlam]
                    · linarith only [h3604, h5032, h5040, hlam]
                  · linarith only [h3078, h5031, h5039, hlam]
                · linarith only [h3078, h5030, h5038, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5045 | h5045
              · linarith only [h0, h4809, h5045, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5047 | h5047
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5048 | h5048
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5049 | h5049
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5050 | h5050
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5051 | h5051
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5052 | h5052
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5053 | h5053
                            · rcases h1bigk with h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h0, hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h3078, hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h3604, hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h3964, hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h5045, h5047, h5049, hc01, hlam, hphi, p5054_1, u1elo2]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h5033, hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h5035, hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h5045, hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [hc01, hlam, hphi, p5054_1, u1elo2]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5054_1, u1elo2]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p5054_1, u1elo2]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h0, h5045, hc01, hlam, hphi, p5054_1, u1elo2]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [hc01, hlam, hphi, p5054_1, u1elo3]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5054_1, u1elo3]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h5047, hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h0, h5045, h5047, hc01, hlam, hphi, p5054_1, u1elo2]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [hc01, hlam, hphi, p5054_1, u1elo4]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5054_1, u1elo4]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h5048, hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [h5049, hlam, p5054_0]
                              · have p5054_0 := h5054c.1
                                have p5054_1 := h5054c.2.1
                                have p5054_2 := h5054c.2.2.1
                                have p5054_3 := h5054c.2.2.2
                                linarith only [hlam, p5054_0]
                            · rcases h1bigk with h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h0, hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h3078, hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h3604, hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h3964, hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [hc01, hlam, hphi, p5080_1, u1elo1]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h5033, hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h5035, hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h5045, hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [hc01, hlam, hphi, p5080_1, u1elo2]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5080_1, u1elo2]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p5080_1, u1elo2]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p5080_1, u1elo2]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [hc01, hlam, hphi, p5080_1, u1elo3]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5080_1, u1elo3]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h5047, hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h0, h5045, h5047, hc01, hlam, hphi, p5080_1, u1elo2]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [hc01, hlam, hphi, p5080_1, u1elo4]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5080_1, u1elo4]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h5048, hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [h5049, hlam, p5080_0]
                              · have p5080_0 := h5080c.1
                                have p5080_1 := h5080c.2.1
                                have p5080_2 := h5080c.2.2.1
                                have p5080_3 := h5080c.2.2.2
                                linarith only [hlam, p5080_0]
                          · linarith only [h0, h3078, h5030, h5032, h5035, h5052, hc01, hlam, hphi, u1elo2]
                        · linarith only [h4232, h5031, h5051, hlam]
                      · linarith only [h0, h5033, h5050, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h3078, h3604, h5030, h5032, h5049, hc01, hlam, hphi, u1elo2]
                  · linarith only [h3078, h5031, h5048, hlam]
                · linarith only [h3078, h5030, h5047, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5112 | h5112
          · linarith only [h0, h4232, h5112, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5114 | h5114
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5115 | h5115
              · linarith only [h0, h4809, h5112, h5115, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5117 | h5117
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5118 | h5118
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5119 | h5119
                    · linarith only [h3604, h5032, h5114, h5119, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5121 | h5121
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5122 | h5122
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5123 | h5123
                          · linarith only [h5114, h5115, h5118, h5119, h5123, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5125 | h5125
                            · linarith only [h0, h5115, h5123, h5125, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h1bigk with h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c | h5127c
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h0, hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h3078, hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h3604, hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h3964, hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [hc01, hlam, hphi, p5127_1, u1elo1]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h5112, hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h3604, h5115, h5123, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5127_1]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h5115, hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [hc01, hlam, hphi, p5127_1, u1elo2]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h5114, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5127_1, u1elo2]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h3604, hc01, hlam, hphi, p5127_1, u1elo2]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h3964, hc01, hlam, hphi, p5127_1, u1elo2]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h5114, hc01, hlam, hphi, p5127_1, u1elo1]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h5114, hlam, p5127_1]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h5117, hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h5119, hlam, p5127_1]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [hc01, hlam, hphi, p5127_1, u1elo4]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, p5127_1, u1elo4]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h5118, hlam, p5127_0]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [h3604, h5118, hc01, hlam, hphi, p5127_1, u1elo2]
                              · have p5127_0 := h5127c.1
                                have p5127_1 := h5127c.2.1
                                have p5127_2 := h5127c.2.2.1
                                have p5127_3 := h5127c.2.2.2
                                linarith only [hlam, p5127_0]
                        · linarith only [h0, h3078, h4232, h5031, h5122, hc01, hlam, hphi, u1elo2]
                      · linarith only [h3604, h5112, h5114, h5121, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3078, h5031, h5118, hlam]
                · linarith only [h3078, h5030, h5117, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5157 | h5157
              · linarith only [h0, h4809, h5157, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5159 | h5159
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5160 | h5160
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5161 | h5161
                    · linarith only [h3604, h5032, h5159, h5161, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5163 | h5163
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5164 | h5164
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5165 | h5165
                          · linarith only [h0, h5114, h5161, h5165, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h5114, h5165, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h3078, h4232, h5031, h5164, hc01, hlam, hphi, u1elo2]
                      · linarith only [h0, h5112, h5163, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3078, h5031, h5160, hlam]
                · linarith only [h3078, h5030, h5159, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5172 | h5172
        · linarith only [h5030, h5031, h5172, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5174 | h5174
          · linarith only [h0, h4232, h5174, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5176 | h5176
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5177 | h5177
              · linarith only [h0, h4809, h5177, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5179 | h5179
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5180 | h5180
                  · linarith only [h5030, h5031, h5180, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5182 | h5182
                    · linarith only [h3604, h5172, h5176, h5182, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5184 | h5184
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5185 | h5185
                        · linarith only [h0, h5174, h5180, h5185, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h3604, h5174, h5176, h5185, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h3604, h5174, h5176, h5184, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h3078, h5030, h5179, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5190 | h5190
              · linarith only [h0, h4809, h5190, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5192 | h5192
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5193 | h5193
                  · linarith only [h5030, h5031, h5193, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5195 | h5195
                    · linarith only [h3604, h5172, h5192, h5193, h5195, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5197 | h5197
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5198 | h5198
                        · linarith only [h0, h5176, h5192, h5193, h5198, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h5174, h5198, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h5030, h5174, h5197, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · linarith only [h3078, h3604, h5030, h5192, hc01, hlam, hphi, u1elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5203 | h5203
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5204 | h5204
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5205 | h5205
          · linarith only [h0, h4232, h5205, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5207 | h5207
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5208 | h5208
              · linarith only [h0, h4809, h5208, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5210 | h5210
                · linarith only [h5030, h5203, h5210, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · linarith only [h5205, h5207, h5210, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5213 | h5213
              · linarith only [h0, h4809, h5213, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5215 | h5215
                · linarith only [h0, h4809, h5030, h5203, h5215, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5217 | h5217
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5218 | h5218
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5219 | h5219
                      · linarith only [h0, h5213, h5215, h5217, h5219, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h5205, h5219, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h3078, h5203, h5204, h5215, h5218, hlam]
                  · linarith only [h3078, h5203, h5217, hlam]
        · linarith only [h5030, h5203, h5204, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5225 | h5225
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5226 | h5226
          · linarith only [h0, h4232, h5226, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5228 | h5228
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5229 | h5229
              · linarith only [h0, h4809, h5229, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5231 | h5231
                · linarith only [h3078, h5030, h5231, hc01, hlam, hphi, u1elo2]
                · linarith only [h5226, h5228, h5231, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5234 | h5234
              · linarith only [h0, h4809, h5234, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5236 | h5236
                · linarith only [h0, h4232, h5030, h5236, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5238 | h5238
                  · linarith only [h0, h4232, h5203, h5236, h5238, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5240 | h5240
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5241 | h5241
                      · linarith only [h0, h5226, h5236, h5241, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h5226, h5241, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h3604, h5225, h5240, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5245 | h5245
          · linarith only [h0, h4232, h5245, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5247 | h5247
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5248 | h5248
              · linarith only [h0, h4809, h5248, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5250 | h5250
                · linarith only [h0, h4232, h5030, h5250, hc01, hlam, hphi, u1elo2]
                · linarith only [h5245, h5247, h5250, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5253 | h5253
              · linarith only [h0, h4809, h5253, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5255 | h5255
                · linarith only [h0, h4232, h5030, h5255, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5257 | h5257
                  · linarith only [h0, h4232, h5203, h5255, h5257, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5259 | h5259
                    · linarith only [h0, h4232, h5030, h5225, h5259, hc01, hlam, hphi, u1elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5261 | h5261
                      · linarith only [h0, h5245, h5255, h5261, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h5245, h5261, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 10528000 in
set_option maxHeartbeats 10528000 in
theorem r1l7_21_15_M_LI_L_I_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3078 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3604 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3964 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4232 | h4232
  · exact r1l7_21_15_M_LI_L_I_x1_x1_x1_x1_x0 m hb1 hb5 h0 h3078 h3604 h3964 h4232
  · exact r1l7_21_15_M_LI_L_I_x1_x1_x1_x1_x1 m hb1 hb5 h0 h3078 h3604 h3964 h4232

set_option maxHeartbeats 10528000 in
set_option maxHeartbeats 10528000 in
theorem r1l7_21_15_M_LI_L_I_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3078 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3604 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3964 | h3964
  · exact r1l7_21_15_M_LI_L_I_x1_x1_x1_x0 m hb1 hb5 h0 h3078 h3604 h3964
  · exact r1l7_21_15_M_LI_L_I_x1_x1_x1_x1 m hb1 hb5 h0 h3078 h3604 h3964

set_option maxHeartbeats 10528000 in
set_option maxHeartbeats 10528000 in
theorem r1l7_21_15_M_LI_L_I_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3078 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h3604 | h3604
  · exact r1l7_21_15_M_LI_L_I_x1_x1_x0 m hb1 hb5 h0 h3078 h3604
  · exact r1l7_21_15_M_LI_L_I_x1_x1_x1 m hb1 hb5 h0 h3078 h3604

set_option maxHeartbeats 10528000 in
set_option maxHeartbeats 10528000 in
theorem r1l7_21_15_M_LI_L_I_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h3078 | h3078
  · exact r1l7_21_15_M_LI_L_I_x1_x0 m hb1 hb5 h0 h3078
  · exact r1l7_21_15_M_LI_L_I_x1_x1 m hb1 hb5 h0 h3078

set_option maxHeartbeats 10528000 in
set_option maxHeartbeats 10528000 in
theorem r1l7_21_15_M_LI_L_I (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_15_M_LI_L_I_x0 m hb1 hb5 h0
  · exact r1l7_21_15_M_LI_L_I_x1 m hb1 hb5 h0

end R2N4
