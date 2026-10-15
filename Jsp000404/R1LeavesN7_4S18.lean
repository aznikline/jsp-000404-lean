import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14861 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14862 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14863 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14864 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h14865 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h14866 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h14867 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h14856 := hg14856
  rcases m.htr 2 3 5 (by decide) (by decide) with h14868 | h14868
  · rcases m.htr 2 4 5 (by decide) (by decide) with h14869 | h14869
    · rcases m.htr 3 4 5 (by decide) (by decide) with h14870 | h14870
      · rcases h1bigk with h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c | h14871c
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h0, hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h11385, hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h12794, hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h13812, hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          rcases p14871_3 (m.d 0 1) (by simp) with h14877 | h14877
          · linarith only [h14877, hlam, p14871_0]
          · rcases p14871_3 (m.d 1 2) (by simp) with h14879 | h14879
            · rcases p14871_3 (m.d 1 3) (by simp) with h14880 | h14880
              · linarith only [h14861, h14880, hlam]
              · linarith only [h11385, h14880, hlam]
            · linarith only [h14879, hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h11385, hc01, hc12, hlam, hphi, p14871_1]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h12794, hc01, hc12, hlam, hphi, p14871_1]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h13812, hc01, hc12, hlam, hphi, p14871_1]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          rcases p14871_3 (m.d 0 1) (by simp) with h14888 | h14888
          · linarith only [h14888, hlam, p14871_0]
          · rcases p14871_3 (m.d 1 2) (by simp) with h14890 | h14890
            · rcases p14871_3 (m.d 1 3) (by simp) with h14891 | h14891
              · rcases p14871_3 (m.d 1 4) (by simp) with h14892 | h14892
                · linarith only [h14864, h14892, hlam]
                · linarith only [h12794, h14892, hlam]
              · linarith only [h14891, hlam, p14871_0]
            · linarith only [h0, h14890, hlam]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h14861, hlam, p14871_1]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h13812, h14866, hc01, hc13, hlam, hphi, p14871_1]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h13812, h14861, hc01, hc12, hlam, hphi, p14871_1]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          rcases p14871_3 (m.d 0 1) (by simp) with h14901 | h14901
          · linarith only [h14901, hlam, p14871_0]
          · rcases p14871_3 (m.d 1 2) (by simp) with h14903 | h14903
            · rcases p14871_3 (m.d 1 3) (by simp) with h14904 | h14904
              · rcases p14871_3 (m.d 1 4) (by simp) with h14905 | h14905
                · rcases p14871_3 (m.d 1 5) (by simp) with h14906 | h14906
                  · linarith only [h14866, h14906, hlam]
                  · linarith only [h13812, h14906, hlam]
                · linarith only [h14905, hlam, p14871_0]
              · linarith only [h11385, h14904, hlam]
            · linarith only [h0, h14903, hlam]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h14862, hlam, p14871_1]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h14864, hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h13812, hc01, hc14, hlam, hphi, p14871_1]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          rcases p14871_3 (m.d 0 1) (by simp) with h14916 | h14916
          · linarith only [h14916, hlam, p14871_0]
          · rcases p14871_3 (m.d 1 2) (by simp) with h14918 | h14918
            · rcases p14871_3 (m.d 1 3) (by simp) with h14919 | h14919
              · rcases p14871_3 (m.d 1 4) (by simp) with h14920 | h14920
                · rcases p14871_3 (m.d 1 5) (by simp) with h14921 | h14921
                  · rcases h3bigk with h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c | h14922c
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h11385, hlam, p14922_1]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h11385, h14861, h14867, h14870, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14922_1]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h11385, h14861, h14870, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14922_1]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      rcases p14922_3 (m.d 0 3) (by simp) with h14927 | h14927
                      · rcases p14922_3 (m.d 1 3) (by simp) with h14928 | h14928
                        · rcases p14922_3 (m.d 2 3) (by simp) with h14929 | h14929
                          · linarith only [h14856, h14929, hlam]
                          · linarith only [h14868, h14929, hlam]
                        · linarith only [h14865, h14928, hlam]
                      · linarith only [h14927, hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h11385, h14861, hc01, hc12, hlam, hphi, p14922_1]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14861, h14867, h14870, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14922_1]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14861, h14870, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14922_1]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      rcases p14922_3 (m.d 0 3) (by simp) with h14938 | h14938
                      · linarith only [h11385, h14938, hlam]
                      · linarith only [h14859, h14938, hlam]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14856, hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14861, hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14856, h14870, hc03, hc45, hlam, hphi, ht0b, ht5b, p14922_1]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h0, h14856, h14870, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14922_1]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14858, hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14864, hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14867, hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h0, h14857, h14867, h14870, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14922_1]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14859, hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14865, hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14868, hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [h14870, hlam, p14922_0]
                    · have p14922_0 := h14922c.1
                      have p14922_1 := h14922c.2.1
                      have p14922_2 := h14922c.2.2.1
                      have p14922_3 := h14922c.2.2.2
                      linarith only [hlam, p14922_0]
                  · linarith only [h14921, hlam, p14871_0]
                · linarith only [h12794, h14920, hlam]
              · linarith only [h11385, h14919, hlam]
            · linarith only [h0, h14918, hlam]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h14863, hlam, p14871_1]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h14865, hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [h14866, hlam, p14871_0]
        · have p14871_0 := h14871c.1
          have p14871_1 := h14871c.2.1
          have p14871_2 := h14871c.2.2.1
          have p14871_3 := h14871c.2.2.2
          linarith only [hlam, p14871_0]
      · rcases h1bigk with h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h0, hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h11385, hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h12794, hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h13812, hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          rcases p14964_3 (m.d 0 1) (by simp) with h14970 | h14970
          · linarith only [h14970, hlam, p14964_0]
          · rcases p14964_3 (m.d 1 2) (by simp) with h14972 | h14972
            · rcases p14964_3 (m.d 1 3) (by simp) with h14973 | h14973
              · linarith only [h14861, h14973, hlam]
              · linarith only [h11385, h14973, hlam]
            · linarith only [h14972, hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h11385, hc01, hc12, hlam, hphi, p14964_1]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h12794, hc01, hc12, hlam, hphi, p14964_1]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h13812, hc01, hc12, hlam, hphi, p14964_1]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          rcases p14964_3 (m.d 0 1) (by simp) with h14981 | h14981
          · linarith only [h14981, hlam, p14964_0]
          · rcases p14964_3 (m.d 1 2) (by simp) with h14983 | h14983
            · rcases p14964_3 (m.d 1 3) (by simp) with h14984 | h14984
              · rcases p14964_3 (m.d 1 4) (by simp) with h14985 | h14985
                · linarith only [h14864, h14985, hlam]
                · linarith only [h12794, h14985, hlam]
              · linarith only [h14984, hlam, p14964_0]
            · linarith only [h0, h14983, hlam]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h14861, hlam, p14964_1]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h12794, h14857, h14869, h14870, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14964_1]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h13812, h14861, hc01, hc12, hlam, hphi, p14964_1]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          rcases p14964_3 (m.d 0 1) (by simp) with h14994 | h14994
          · linarith only [h14994, hlam, p14964_0]
          · rcases p14964_3 (m.d 1 2) (by simp) with h14996 | h14996
            · rcases p14964_3 (m.d 1 3) (by simp) with h14997 | h14997
              · rcases p14964_3 (m.d 1 4) (by simp) with h14998 | h14998
                · rcases p14964_3 (m.d 1 5) (by simp) with h14999 | h14999
                  · linarith only [h14866, h14999, hlam]
                  · linarith only [h13812, h14999, hlam]
                · linarith only [h14998, hlam, p14964_0]
              · linarith only [h11385, h14997, hlam]
            · linarith only [h0, h14996, hlam]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h14862, hlam, p14964_1]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h14864, hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h13812, hc01, hc14, hlam, hphi, p14964_1]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          rcases p14964_3 (m.d 0 1) (by simp) with h15009 | h15009
          · linarith only [h15009, hlam, p14964_0]
          · rcases p14964_3 (m.d 1 2) (by simp) with h15011 | h15011
            · rcases p14964_3 (m.d 1 3) (by simp) with h15012 | h15012
              · rcases p14964_3 (m.d 1 4) (by simp) with h15013 | h15013
                · rcases p14964_3 (m.d 1 5) (by simp) with h15014 | h15014
                  · rcases h3bigk with h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c | h15015c
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h11385, hlam, p15015_1]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h0, h14856, h14867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15015_1]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      rcases p15015_3 (m.d 0 3) (by simp) with h15019 | h15019
                      · rcases p15015_3 (m.d 1 3) (by simp) with h15020 | h15020
                        · rcases p15015_3 (m.d 2 3) (by simp) with h15021 | h15021
                          · linarith only [h14856, h15021, hlam]
                          · linarith only [h14867, h15021, hlam]
                        · linarith only [h14864, h15020, hlam]
                      · linarith only [h15019, hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      rcases p15015_3 (m.d 0 3) (by simp) with h15026 | h15026
                      · rcases p15015_3 (m.d 1 3) (by simp) with h15027 | h15027
                        · rcases p15015_3 (m.d 2 3) (by simp) with h15028 | h15028
                          · linarith only [h14856, h15028, hlam]
                          · linarith only [h14868, h15028, hlam]
                        · linarith only [h14865, h15027, hlam]
                      · linarith only [h15026, hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h11385, h14861, hc01, hc12, hlam, hphi, p15015_1]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h14861, h14867, h14869, h14870, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15015_1]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      rcases p15015_3 (m.d 0 3) (by simp) with h15036 | h15036
                      · linarith only [h11385, h15036, hlam]
                      · linarith only [h14858, h15036, hlam]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      rcases p15015_3 (m.d 0 3) (by simp) with h15039 | h15039
                      · linarith only [h11385, h15039, hlam]
                      · linarith only [h14859, h15039, hlam]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h14856, hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h14861, hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h0, h14856, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15015_1]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h0, h14856, h14870, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15015_1]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h14858, hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h14864, hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h14867, hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h14870, hlam, p15015_1]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h14859, hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h14865, hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h14868, hlam, p15015_0]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [h14859, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p15015_1]
                    · have p15015_0 := h15015c.1
                      have p15015_1 := h15015c.2.1
                      have p15015_2 := h15015c.2.2.1
                      have p15015_3 := h15015c.2.2.2
                      linarith only [hlam, p15015_0]
                  · linarith only [h15014, hlam, p14964_0]
                · linarith only [h12794, h15013, hlam]
              · linarith only [h11385, h15012, hlam]
            · linarith only [h0, h15011, hlam]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h14863, hlam, p14964_1]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h14865, hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [h14866, hlam, p14964_0]
        · have p14964_0 := h14964c.1
          have p14964_1 := h14964c.2.1
          have p14964_2 := h14964c.2.2.1
          have p14964_3 := h14964c.2.2.2
          linarith only [hlam, p14964_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h15065 | h15065
      · linarith only [h0, h14856, h14867, h14869, h15065, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h1bigk with h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c | h15067c
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h0, hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h11385, hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h12794, hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h13812, hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          rcases p15067_3 (m.d 0 1) (by simp) with h15073 | h15073
          · linarith only [h15073, hlam, p15067_0]
          · rcases p15067_3 (m.d 1 2) (by simp) with h15075 | h15075
            · rcases p15067_3 (m.d 1 3) (by simp) with h15076 | h15076
              · linarith only [h14861, h15076, hlam]
              · linarith only [h11385, h15076, hlam]
            · linarith only [h15075, hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h12794, h14860, h14864, h14869, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15067_1]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h12794, h14860, h14867, h14869, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15067_1]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h13812, hc01, hc12, hlam, hphi, p15067_1]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          rcases p15067_3 (m.d 0 1) (by simp) with h15084 | h15084
          · linarith only [h15084, hlam, p15067_0]
          · rcases p15067_3 (m.d 1 2) (by simp) with h15086 | h15086
            · rcases p15067_3 (m.d 1 3) (by simp) with h15087 | h15087
              · rcases p15067_3 (m.d 1 4) (by simp) with h15088 | h15088
                · linarith only [h14864, h15088, hlam]
                · linarith only [h12794, h15088, hlam]
              · linarith only [h15087, hlam, p15067_0]
            · linarith only [h0, h15086, hlam]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h14861, hlam, p15067_1]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h12794, h14860, h14867, h14869, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15067_1]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h13812, h14861, hc01, hc12, hlam, hphi, p15067_1]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          rcases p15067_3 (m.d 0 1) (by simp) with h15097 | h15097
          · linarith only [h15097, hlam, p15067_0]
          · rcases p15067_3 (m.d 1 2) (by simp) with h15099 | h15099
            · rcases p15067_3 (m.d 1 3) (by simp) with h15100 | h15100
              · rcases p15067_3 (m.d 1 4) (by simp) with h15101 | h15101
                · rcases p15067_3 (m.d 1 5) (by simp) with h15102 | h15102
                  · linarith only [h14866, h15102, hlam]
                  · linarith only [h13812, h15102, hlam]
                · linarith only [h15101, hlam, p15067_0]
              · linarith only [h11385, h15100, hlam]
            · linarith only [h0, h15099, hlam]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h14862, hlam, p15067_1]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h14864, hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h13812, hc01, hc14, hlam, hphi, p15067_1]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          rcases p15067_3 (m.d 0 1) (by simp) with h15112 | h15112
          · linarith only [h15112, hlam, p15067_0]
          · rcases p15067_3 (m.d 1 2) (by simp) with h15114 | h15114
            · rcases p15067_3 (m.d 1 3) (by simp) with h15115 | h15115
              · rcases p15067_3 (m.d 1 4) (by simp) with h15116 | h15116
                · rcases p15067_3 (m.d 1 5) (by simp) with h15117 | h15117
                  · rcases h3bigk with h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c | h15118c
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h11385, hlam, p15118_1]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h0, h14856, h14867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15118_1]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      rcases p15118_3 (m.d 0 3) (by simp) with h15122 | h15122
                      · rcases p15118_3 (m.d 1 3) (by simp) with h15123 | h15123
                        · rcases p15118_3 (m.d 2 3) (by simp) with h15124 | h15124
                          · linarith only [h14856, h15124, hlam]
                          · linarith only [h14867, h15124, hlam]
                        · linarith only [h14864, h15123, hlam]
                      · linarith only [h15122, hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      rcases p15118_3 (m.d 0 3) (by simp) with h15129 | h15129
                      · rcases p15118_3 (m.d 1 3) (by simp) with h15130 | h15130
                        · rcases p15118_3 (m.d 2 3) (by simp) with h15131 | h15131
                          · linarith only [h14856, h15131, hlam]
                          · linarith only [h14868, h15131, hlam]
                        · linarith only [h14865, h15130, hlam]
                      · linarith only [h15129, hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h11385, h14861, hc01, hc12, hlam, hphi, p15118_1]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h14861, h14867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15118_1]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      rcases p15118_3 (m.d 0 3) (by simp) with h15139 | h15139
                      · linarith only [h11385, h15139, hlam]
                      · linarith only [h14858, h15139, hlam]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      rcases p15118_3 (m.d 0 3) (by simp) with h15142 | h15142
                      · linarith only [h11385, h15142, hlam]
                      · linarith only [h14859, h15142, hlam]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h14856, hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h14861, hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h0, h14856, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15118_1]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h0, h14856, h15065, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15118_1]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h14858, hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h14864, hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h14867, hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h15065, hlam, p15118_1]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h14859, hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h14865, hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h14868, hlam, p15118_0]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [h14859, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p15118_1]
                    · have p15118_0 := h15118c.1
                      have p15118_1 := h15118c.2.1
                      have p15118_2 := h15118c.2.2.1
                      have p15118_3 := h15118c.2.2.2
                      linarith only [hlam, p15118_0]
                  · linarith only [h15117, hlam, p15067_0]
                · linarith only [h12794, h15116, hlam]
              · linarith only [h11385, h15115, hlam]
            · linarith only [h0, h15114, hlam]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h14863, hlam, p15067_1]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h14865, hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [h14866, hlam, p15067_0]
        · have p15067_0 := h15067c.1
          have p15067_1 := h15067c.2.1
          have p15067_2 := h15067c.2.2.1
          have p15067_3 := h15067c.2.2.2
          linarith only [hlam, p15067_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h15168 | h15168
    · linarith only [h14867, h14868, h15168, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h15170 | h15170
      · linarith only [h14859, h14867, h14868, h15168, h15170, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases h1bigk with h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c | h15172c
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h0, hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h11385, hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h12794, hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h13812, hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          rcases p15172_3 (m.d 0 1) (by simp) with h15178 | h15178
          · linarith only [h15178, hlam, p15172_0]
          · rcases p15172_3 (m.d 1 2) (by simp) with h15180 | h15180
            · rcases p15172_3 (m.d 1 3) (by simp) with h15181 | h15181
              · linarith only [h14861, h15181, hlam]
              · linarith only [h11385, h15181, hlam]
            · linarith only [h15180, hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h12794, h14860, h14864, h14868, h15170, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15172_1]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h12794, h14860, h14868, h15170, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15172_1]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h13812, hc01, hc12, hlam, hphi, p15172_1]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          rcases p15172_3 (m.d 0 1) (by simp) with h15189 | h15189
          · linarith only [h15189, hlam, p15172_0]
          · rcases p15172_3 (m.d 1 2) (by simp) with h15191 | h15191
            · rcases p15172_3 (m.d 1 3) (by simp) with h15192 | h15192
              · rcases p15172_3 (m.d 1 4) (by simp) with h15193 | h15193
                · linarith only [h14864, h15193, hlam]
                · linarith only [h12794, h15193, hlam]
              · linarith only [h15192, hlam, p15172_0]
            · linarith only [h0, h15191, hlam]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h14861, hlam, p15172_1]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h12794, h14860, h14867, h14868, h15170, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15172_1]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h13812, h14860, h14861, h14867, h14868, h15170, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15172_1]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          rcases p15172_3 (m.d 0 1) (by simp) with h15202 | h15202
          · linarith only [h15202, hlam, p15172_0]
          · rcases p15172_3 (m.d 1 2) (by simp) with h15204 | h15204
            · rcases p15172_3 (m.d 1 3) (by simp) with h15205 | h15205
              · rcases p15172_3 (m.d 1 4) (by simp) with h15206 | h15206
                · rcases p15172_3 (m.d 1 5) (by simp) with h15207 | h15207
                  · linarith only [h14866, h15207, hlam]
                  · linarith only [h13812, h15207, hlam]
                · linarith only [h15206, hlam, p15172_0]
              · linarith only [h11385, h15205, hlam]
            · linarith only [h0, h15204, hlam]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h14862, hlam, p15172_1]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h14864, hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h13812, h14860, h14867, h14868, h15170, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15172_1]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          rcases p15172_3 (m.d 0 1) (by simp) with h15217 | h15217
          · linarith only [h15217, hlam, p15172_0]
          · rcases p15172_3 (m.d 1 2) (by simp) with h15219 | h15219
            · rcases p15172_3 (m.d 1 3) (by simp) with h15220 | h15220
              · rcases p15172_3 (m.d 1 4) (by simp) with h15221 | h15221
                · rcases p15172_3 (m.d 1 5) (by simp) with h15222 | h15222
                  · rcases h3bigk with h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c | h15223c
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h11385, hlam, p15223_1]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14867, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p15223_1]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      rcases p15223_3 (m.d 0 3) (by simp) with h15227 | h15227
                      · rcases p15223_3 (m.d 1 3) (by simp) with h15228 | h15228
                        · rcases p15223_3 (m.d 2 3) (by simp) with h15229 | h15229
                          · linarith only [h14856, h15229, hlam]
                          · linarith only [h14867, h15229, hlam]
                        · linarith only [h14864, h15228, hlam]
                      · linarith only [h15227, hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h11385, h14861, h14867, h14868, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15223_1]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h11385, h14861, hc01, hc12, hlam, hphi, p15223_1]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14861, h14867, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15223_1]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      rcases p15223_3 (m.d 0 3) (by simp) with h15238 | h15238
                      · linarith only [h11385, h15238, hlam]
                      · linarith only [h14858, h15238, hlam]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14861, h14867, h14868, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15223_1]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14856, hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14861, hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14858, h14860, h14868, h15170, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p15223_1]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14868, hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14858, hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14864, hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14867, hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h15170, hlam, p15223_1]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14859, hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14865, hlam, p15223_0]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h14858, h14860, h15170, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15223_1]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [h11385, h14858, h14860, h14861, h15170, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15223_1]
                    · have p15223_0 := h15223c.1
                      have p15223_1 := h15223c.2.1
                      have p15223_2 := h15223c.2.2.1
                      have p15223_3 := h15223c.2.2.2
                      linarith only [hlam, p15223_0]
                  · linarith only [h15222, hlam, p15172_0]
                · linarith only [h12794, h15221, hlam]
              · linarith only [h11385, h15220, hlam]
            · linarith only [h0, h15219, hlam]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h14863, hlam, p15172_1]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h14865, hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [h14866, hlam, p15172_0]
        · have p15172_0 := h15172c.1
          have p15172_1 := h15172c.2.1
          have p15172_2 := h15172c.2.2.1
          have p15172_3 := h15172c.2.2.2
          linarith only [hlam, p15172_0]

end R2N4
