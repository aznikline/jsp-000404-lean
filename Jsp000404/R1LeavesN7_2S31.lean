import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x0_x0_x0_x0_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h20414 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h20415 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h20416 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h20417 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h20418 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h20419 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h20420 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h21506 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h21783 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 3 4 5 (by decide) (by decide) with h21784 | h21784
  · rcases h0bigk with h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c | h21785c
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [hlam, p21785_0]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [h0, hlam, p21785_1]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [h14396, hlam, p21785_0]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [h16915, hlam, p21785_1]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [h18815, hlam, p21785_1]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      rcases p21785_3 (m.d 0 1) (by simp) with h21791 | h21791
      · linarith only [h0, h21791, hlam]
      · rcases p21785_3 (m.d 0 2) (by simp) with h21793 | h21793
        · rcases p21785_3 (m.d 0 3) (by simp) with h21794 | h21794
          · linarith only [h20408, h21794, hlam]
          · linarith only [h14396, h21794, hlam]
        · linarith only [h0, h21793, hlam]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [hlam, p21785_0]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [h0, h20411, h21506, h21784, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21785_1]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      rcases p21785_3 (m.d 0 1) (by simp) with h21800 | h21800
      · linarith only [h0, h21800, hlam]
      · rcases p21785_3 (m.d 0 2) (by simp) with h21802 | h21802
        · rcases p21785_3 (m.d 0 3) (by simp) with h21803 | h21803
          · linarith only [h20408, h21803, hlam]
          · linarith only [h20411, h21803, hlam]
        · linarith only [h20409, h21802, hlam]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      rcases p21785_3 (m.d 0 1) (by simp) with h21807 | h21807
      · linarith only [h0, h21807, hlam]
      · rcases p21785_3 (m.d 0 2) (by simp) with h21809 | h21809
        · rcases p21785_3 (m.d 0 3) (by simp) with h21810 | h21810
          · linarith only [h20408, h21810, hlam]
          · linarith only [h20412, h21810, hlam]
        · linarith only [h20410, h21809, hlam]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      rcases p21785_3 (m.d 0 1) (by simp) with h21814 | h21814
      · linarith only [h14396, h21814, hlam]
      · rcases p21785_3 (m.d 0 2) (by simp) with h21816 | h21816
        · rcases p21785_3 (m.d 0 3) (by simp) with h21817 | h21817
          · rcases p21785_3 (m.d 0 4) (by simp) with h21818 | h21818
            · linarith only [h20411, h21818, hlam]
            · linarith only [h16915, h21818, hlam]
          · linarith only [h14396, h21817, hlam]
        · linarith only [h0, h21816, hlam]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [h20408, hlam, p21785_1]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [hlam, p21785_0]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      rcases p21785_3 (m.d 0 1) (by simp) with h21825 | h21825
      · linarith only [h14396, h21825, hlam]
      · rcases p21785_3 (m.d 0 2) (by simp) with h21827 | h21827
        · rcases p21785_3 (m.d 0 3) (by simp) with h21828 | h21828
          · rcases p21785_3 (m.d 0 4) (by simp) with h21829 | h21829
            · linarith only [h20411, h21829, hlam]
            · rcases p21785_3 (m.d 0 5) (by simp) with h21831 | h21831
              · linarith only [h20412, h21831, hlam]
              · rcases h2bigk with h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c | h21833c
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h0, hlam, p21833_1]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h20408, h20411, h21506, h21784, hlam, p21785_1, p21833_2]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  rcases p21833_3 (m.d 0 2) (by simp) with h21837 | h21837
                  · rcases p21833_3 (m.d 1 2) (by simp) with h21838 | h21838
                    · rcases p21833_3 (m.d 2 3) (by simp) with h21839 | h21839
                      · linarith only [h20408, h21839, hlam]
                      · rcases p21833_3 (m.d 2 4) (by simp) with h21841 | h21841
                        · linarith only [h21841, hlam, p21833_0]
                        · rcases p21833_3 (m.d 2 5) (by simp) with h21843 | h21843
                          · linarith only [h20410, h21843, hlam]
                          · rcases h3bigk with h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c | h21845c
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h14396, hlam, p21845_1]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              rcases p21845_3 (m.d 0 3) (by simp) with h21848 | h21848
                              · rcases p21845_3 (m.d 1 3) (by simp) with h21849 | h21849
                                · rcases p21845_3 (m.d 2 3) (by simp) with h21850 | h21850
                                  · linarith only [h20408, h21850, hlam]
                                  · rcases p21845_3 (m.d 3 4) (by simp) with h21852 | h21852
                                    · linarith only [h20411, h21852, hlam]
                                    · linarith only [h20420, h21852, hlam]
                                · linarith only [h20414, h21849, hlam]
                              · linarith only [h20408, h21848, hlam]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h20408, h21506, h21784, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21845_1]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h0, h20408, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21845_1]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p21845_1]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              rcases p21845_3 (m.d 0 3) (by simp) with h21861 | h21861
                              · linarith only [h14396, h21861, hlam]
                              · linarith only [h20408, h21861, hlam]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h20414, h21506, h21784, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21845_1]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21845_1]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h20408, hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h20414, hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h20420, hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h21506, hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h20411, hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h20417, hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h20411, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21785_1, p21845_1]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h14396, h20411, h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21785_1, p21845_1]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h20412, hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h20418, hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [hc23, hc35, hlam, hphi, p21845_1]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [h21784, hlam, p21845_0]
                            · have p21845_0 := h21845c.1
                              have p21845_1 := h21845c.2.1
                              have p21845_2 := h21845c.2.2.1
                              have p21845_3 := h21845c.2.2.2
                              linarith only [hlam, p21845_0]
                    · linarith only [h20415, h21838, hlam]
                  · linarith only [h21837, hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  rcases p21833_3 (m.d 0 2) (by simp) with h21883 | h21883
                  · rcases p21833_3 (m.d 1 2) (by simp) with h21884 | h21884
                    · rcases p21833_3 (m.d 2 3) (by simp) with h21885 | h21885
                      · linarith only [h20408, h21885, hlam]
                      · rcases p21833_3 (m.d 2 4) (by simp) with h21887 | h21887
                        · linarith only [h20409, h21887, hlam]
                        · linarith only [h21783, h21887, hlam]
                    · linarith only [h20416, h21884, hlam]
                  · linarith only [h21883, hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h20408, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p21785_1, p21833_1]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h0, h20408, h20411, h20420, hlam, p21785_1, p21833_2]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  rcases p21833_3 (m.d 0 2) (by simp) with h21895 | h21895
                  · linarith only [h0, h21895, hlam]
                  · linarith only [h20409, h21895, hlam]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  rcases p21833_3 (m.d 0 2) (by simp) with h21898 | h21898
                  · linarith only [h0, h21898, hlam]
                  · linarith only [h20410, h21898, hlam]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h20408, hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h20414, hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h20420, hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h21506, hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h20409, hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h20415, hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h20408, h20411, h20420, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21785_1, p21833_1]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h0, h20408, h20411, h20420, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p21785_1, p21833_1]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h20410, hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h20416, hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h0, h20408, h20410, h20413, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21785_1, p21833_1]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [h21783, hlam, p21833_0]
                · have p21833_0 := h21833c.1
                  have p21833_1 := h21833c.2.1
                  have p21833_2 := h21833c.2.2.1
                  have p21833_3 := h21833c.2.2.2
                  linarith only [hlam, p21833_0]
          · linarith only [h20411, h21828, hlam]
        · linarith only [h20409, h21827, hlam]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      rcases p21785_3 (m.d 0 1) (by simp) with h21918 | h21918
      · linarith only [h14396, h21918, hlam]
      · rcases p21785_3 (m.d 0 2) (by simp) with h21920 | h21920
        · rcases p21785_3 (m.d 0 3) (by simp) with h21921 | h21921
          · rcases p21785_3 (m.d 0 4) (by simp) with h21922 | h21922
            · linarith only [h20411, h21922, hlam]
            · linarith only [h20413, h21922, hlam]
          · linarith only [h20412, h21921, hlam]
        · linarith only [h20410, h21920, hlam]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      rcases p21785_3 (m.d 0 1) (by simp) with h21927 | h21927
      · linarith only [h16915, h21927, hlam]
      · rcases p21785_3 (m.d 0 2) (by simp) with h21929 | h21929
        · rcases p21785_3 (m.d 0 3) (by simp) with h21930 | h21930
          · rcases p21785_3 (m.d 0 4) (by simp) with h21931 | h21931
            · rcases p21785_3 (m.d 0 5) (by simp) with h21932 | h21932
              · linarith only [h20413, h21932, hlam]
              · linarith only [h18815, h21932, hlam]
            · linarith only [h16915, h21931, hlam]
          · linarith only [h14396, h21930, hlam]
        · linarith only [h0, h21929, hlam]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [h20409, hlam, p21785_0]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [h20411, hlam, p21785_0]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [hlam, p21785_0]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      rcases p21785_3 (m.d 0 1) (by simp) with h21941 | h21941
      · linarith only [h16915, h21941, hlam]
      · rcases p21785_3 (m.d 0 2) (by simp) with h21943 | h21943
        · rcases p21785_3 (m.d 0 3) (by simp) with h21944 | h21944
          · rcases p21785_3 (m.d 0 4) (by simp) with h21945 | h21945
            · rcases p21785_3 (m.d 0 5) (by simp) with h21946 | h21946
              · linarith only [h20413, h21946, hlam]
              · rcases h2bigk with h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c | h21948c
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h0, hlam, p21948_1]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h20409, h20412, h21506, hlam, p21785_1, p21948_2]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  rcases p21948_3 (m.d 0 2) (by simp) with h21952 | h21952
                  · rcases p21948_3 (m.d 1 2) (by simp) with h21953 | h21953
                    · rcases p21948_3 (m.d 2 3) (by simp) with h21954 | h21954
                      · linarith only [h20408, h21954, hlam]
                      · rcases p21948_3 (m.d 2 4) (by simp) with h21956 | h21956
                        · linarith only [h21956, hlam, p21948_0]
                        · rcases p21948_3 (m.d 2 5) (by simp) with h21958 | h21958
                          · linarith only [h20410, h21958, hlam]
                          · rcases h3bigk with h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c | h21960c
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h14396, hlam, p21960_1]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              rcases p21960_3 (m.d 0 3) (by simp) with h21963 | h21963
                              · rcases p21960_3 (m.d 1 3) (by simp) with h21964 | h21964
                                · rcases p21960_3 (m.d 2 3) (by simp) with h21965 | h21965
                                  · linarith only [h20408, h21965, hlam]
                                  · rcases p21960_3 (m.d 3 4) (by simp) with h21967 | h21967
                                    · linarith only [h20411, h21967, hlam]
                                    · linarith only [h20420, h21967, hlam]
                                · linarith only [h20414, h21964, hlam]
                              · linarith only [h20408, h21963, hlam]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20408, h20420, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21960_1]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h0, h20408, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21960_1]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p21960_1]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              rcases p21960_3 (m.d 0 3) (by simp) with h21976 | h21976
                              · linarith only [h14396, h21976, hlam]
                              · linarith only [h20408, h21976, hlam]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20414, h20420, h21783, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21960_1]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21960_1]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20408, hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20414, hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20420, hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h21506, hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20411, hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20417, hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [hc23, hc34, hlam, hphi, p21960_1]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20411, h21506, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21960_1]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20412, hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20418, hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h20412, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21785_1, p21960_1]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [h21784, hlam, p21960_0]
                            · have p21960_0 := h21960c.1
                              have p21960_1 := h21960c.2.1
                              have p21960_2 := h21960c.2.2.1
                              have p21960_3 := h21960c.2.2.2
                              linarith only [hlam, p21960_0]
                    · linarith only [h20415, h21953, hlam]
                  · linarith only [h21952, hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  rcases p21948_3 (m.d 0 2) (by simp) with h21998 | h21998
                  · rcases p21948_3 (m.d 1 2) (by simp) with h21999 | h21999
                    · rcases p21948_3 (m.d 2 3) (by simp) with h22000 | h22000
                      · linarith only [h20408, h22000, hlam]
                      · rcases p21948_3 (m.d 2 4) (by simp) with h22002 | h22002
                        · linarith only [h20409, h22002, hlam]
                        · linarith only [h21783, h22002, hlam]
                    · linarith only [h20416, h21999, hlam]
                  · linarith only [h21998, hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h20409, h21783, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p21948_1]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h0, h20408, h20411, h20412, h21506, hlam, p21785_1, p21948_2]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  rcases p21948_3 (m.d 0 2) (by simp) with h22010 | h22010
                  · linarith only [h0, h22010, hlam]
                  · linarith only [h20409, h22010, hlam]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  rcases p21948_3 (m.d 0 2) (by simp) with h22013 | h22013
                  · linarith only [h0, h22013, hlam]
                  · linarith only [h20410, h22013, hlam]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h20408, hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h20414, hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h20420, hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h21506, hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h20409, hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h20415, hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  rcases p21948_3 (m.d 0 2) (by simp) with h22023 | h22023
                  · rcases p21948_3 (m.d 1 2) (by simp) with h22024 | h22024
                    · rcases p21948_3 (m.d 2 3) (by simp) with h22025 | h22025
                      · linarith only [h20420, h22025, hlam]
                      · rcases p21948_3 (m.d 2 4) (by simp) with h22027 | h22027
                        · rcases p21948_3 (m.d 2 5) (by simp) with h22028 | h22028
                          · linarith only [h21783, h22028, hlam]
                          · linarith only [h21506, h22028, hlam]
                        · linarith only [h20420, h22027, hlam]
                    · linarith only [h20414, h22024, hlam]
                  · linarith only [h20408, h22023, hlam]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  rcases p21948_3 (m.d 0 2) (by simp) with h22035 | h22035
                  · rcases p21948_3 (m.d 1 2) (by simp) with h22036 | h22036
                    · rcases p21948_3 (m.d 2 3) (by simp) with h22037 | h22037
                      · linarith only [h20420, h22037, hlam]
                      · rcases p21948_3 (m.d 2 4) (by simp) with h22039 | h22039
                        · rcases p21948_3 (m.d 2 5) (by simp) with h22040 | h22040
                          · linarith only [h21783, h22040, hlam]
                          · rcases h3bigk with h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c | h22042c
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h14396, hlam, p22042_1]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              rcases p22042_3 (m.d 0 3) (by simp) with h22045 | h22045
                              · rcases p22042_3 (m.d 1 3) (by simp) with h22046 | h22046
                                · rcases p22042_3 (m.d 2 3) (by simp) with h22047 | h22047
                                  · linarith only [h20408, h22047, hlam]
                                  · rcases p22042_3 (m.d 3 4) (by simp) with h22049 | h22049
                                    · linarith only [h20411, h22049, hlam]
                                    · linarith only [h20420, h22049, hlam]
                                · linarith only [h20414, h22046, hlam]
                              · linarith only [h20408, h22045, hlam]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20408, h20420, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22042_1]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h0, h20408, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22042_1]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p22042_1]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              rcases p22042_3 (m.d 0 3) (by simp) with h22058 | h22058
                              · linarith only [h14396, h22058, hlam]
                              · linarith only [h20408, h22058, hlam]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20414, h20420, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21948_1, p22042_1]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22042_1]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20408, hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20414, hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20420, hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h21506, hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20411, hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20417, hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [hc23, hc34, hlam, hphi, p22042_1]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20411, h21506, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22042_1]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20412, hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20418, hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h20412, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p21785_1, p22042_1]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [h21784, hlam, p22042_0]
                            · have p22042_0 := h22042c.1
                              have p22042_1 := h22042c.2.1
                              have p22042_2 := h22042c.2.2.1
                              have p22042_3 := h22042c.2.2.2
                              linarith only [hlam, p22042_0]
                        · linarith only [h21783, h22039, hlam]
                    · linarith only [h20416, h22036, hlam]
                  · linarith only [h20410, h22035, hlam]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h20410, hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h20416, hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h16915, h20410, h20414, h20417, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p21785_1, p21948_1]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [h21783, hlam, p21948_0]
                · have p21948_0 := h21948c.1
                  have p21948_1 := h21948c.2.1
                  have p21948_2 := h21948c.2.2.1
                  have p21948_3 := h21948c.2.2.2
                  linarith only [hlam, p21948_0]
            · linarith only [h20413, h21945, hlam]
          · linarith only [h20412, h21944, hlam]
        · linarith only [h20410, h21943, hlam]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      rcases p21785_3 (m.d 0 1) (by simp) with h22089 | h22089
      · linarith only [h18815, h22089, hlam]
      · rcases p21785_3 (m.d 0 2) (by simp) with h22091 | h22091
        · rcases p21785_3 (m.d 0 3) (by simp) with h22092 | h22092
          · rcases p21785_3 (m.d 0 4) (by simp) with h22093 | h22093
            · rcases p21785_3 (m.d 0 5) (by simp) with h22094 | h22094
              · rcases h2bigk with h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c | h22095c
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [h0, hlam, p22095_1]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  rcases p22095_3 (m.d 0 2) (by simp) with h22098 | h22098
                  · rcases p22095_3 (m.d 1 2) (by simp) with h22099 | h22099
                    · rcases p22095_3 (m.d 2 3) (by simp) with h22100 | h22100
                      · linarith only [h22100, hlam, p22095_0]
                      · rcases p22095_3 (m.d 2 4) (by simp) with h22102 | h22102
                        · linarith only [h20409, h22102, hlam]
                        · linarith only [h20420, h22102, hlam]
                    · linarith only [h20414, h22099, hlam]
                  · linarith only [h22098, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  rcases p22095_3 (m.d 0 2) (by simp) with h22107 | h22107
                  · rcases p22095_3 (m.d 1 2) (by simp) with h22108 | h22108
                    · rcases p22095_3 (m.d 2 3) (by simp) with h22109 | h22109
                      · linarith only [h20408, h22109, hlam]
                      · rcases p22095_3 (m.d 2 4) (by simp) with h22111 | h22111
                        · linarith only [h22111, hlam, p22095_0]
                        · rcases p22095_3 (m.d 2 5) (by simp) with h22113 | h22113
                          · linarith only [h20410, h22113, hlam]
                          · rcases h3bigk with h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c | h22115c
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h14396, hlam, p22115_1]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              rcases p22115_3 (m.d 0 3) (by simp) with h22118 | h22118
                              · rcases p22115_3 (m.d 1 3) (by simp) with h22119 | h22119
                                · rcases p22115_3 (m.d 2 3) (by simp) with h22120 | h22120
                                  · linarith only [h20408, h22120, hlam]
                                  · rcases p22115_3 (m.d 3 4) (by simp) with h22122 | h22122
                                    · linarith only [h20411, h22122, hlam]
                                    · linarith only [h20420, h22122, hlam]
                                · linarith only [h20414, h22119, hlam]
                              · linarith only [h20408, h22118, hlam]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h14396, h20414, h20420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22115_1]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h14396, h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22115_1]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p22115_1]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              rcases p22115_3 (m.d 0 3) (by simp) with h22131 | h22131
                              · linarith only [h14396, h22131, hlam]
                              · linarith only [h20408, h22131, hlam]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h20414, h21506, h21784, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22115_1]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22115_1]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h20408, hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h20414, hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h20420, hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h21506, hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h20411, hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h20417, hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [hc23, hc34, hlam, hphi, p22115_1]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h20408, h20411, h21506, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22115_1]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h20412, hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h20418, hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [hc23, hc35, hlam, hphi, p22115_1]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [h21784, hlam, p22115_0]
                            · have p22115_0 := h22115c.1
                              have p22115_1 := h22115c.2.1
                              have p22115_2 := h22115c.2.2.1
                              have p22115_3 := h22115c.2.2.2
                              linarith only [hlam, p22115_0]
                    · linarith only [h20415, h22108, hlam]
                  · linarith only [h22107, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  rcases p22095_3 (m.d 0 2) (by simp) with h22153 | h22153
                  · rcases p22095_3 (m.d 1 2) (by simp) with h22154 | h22154
                    · rcases p22095_3 (m.d 2 3) (by simp) with h22155 | h22155
                      · linarith only [h20408, h22155, hlam]
                      · rcases p22095_3 (m.d 2 4) (by simp) with h22157 | h22157
                        · linarith only [h20409, h22157, hlam]
                        · linarith only [h21783, h22157, hlam]
                    · linarith only [h20416, h22154, hlam]
                  · linarith only [h22153, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [h20409, h21783, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22095_1]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  rcases p22095_3 (m.d 0 2) (by simp) with h22164 | h22164
                  · linarith only [h0, h22164, hlam]
                  · linarith only [h20408, h22164, hlam]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  rcases p22095_3 (m.d 0 2) (by simp) with h22167 | h22167
                  · linarith only [h0, h22167, hlam]
                  · linarith only [h20409, h22167, hlam]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  rcases p22095_3 (m.d 0 2) (by simp) with h22170 | h22170
                  · linarith only [h0, h22170, hlam]
                  · linarith only [h20410, h22170, hlam]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [h20408, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [h20414, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [h20420, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [h21506, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [h20409, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [h20415, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  rcases p22095_3 (m.d 0 2) (by simp) with h22180 | h22180
                  · rcases p22095_3 (m.d 1 2) (by simp) with h22181 | h22181
                    · rcases p22095_3 (m.d 2 3) (by simp) with h22182 | h22182
                      · linarith only [h20420, h22182, hlam]
                      · rcases p22095_3 (m.d 2 4) (by simp) with h22184 | h22184
                        · rcases p22095_3 (m.d 2 5) (by simp) with h22185 | h22185
                          · linarith only [h21783, h22185, hlam]
                          · linarith only [h21506, h22185, hlam]
                        · linarith only [h20420, h22184, hlam]
                    · linarith only [h20414, h22181, hlam]
                  · linarith only [h20408, h22180, hlam]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  rcases p22095_3 (m.d 0 2) (by simp) with h22192 | h22192
                  · rcases p22095_3 (m.d 1 2) (by simp) with h22193 | h22193
                    · rcases p22095_3 (m.d 2 3) (by simp) with h22194 | h22194
                      · linarith only [h20420, h22194, hlam]
                      · rcases p22095_3 (m.d 2 4) (by simp) with h22196 | h22196
                        · rcases p22095_3 (m.d 2 5) (by simp) with h22197 | h22197
                          · linarith only [h21783, h22197, hlam]
                          · rcases h3bigk with h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c | h22199c
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h14396, hlam, p22199_1]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              rcases p22199_3 (m.d 0 3) (by simp) with h22202 | h22202
                              · rcases p22199_3 (m.d 1 3) (by simp) with h22203 | h22203
                                · rcases p22199_3 (m.d 2 3) (by simp) with h22204 | h22204
                                  · linarith only [h20408, h22204, hlam]
                                  · rcases p22199_3 (m.d 3 4) (by simp) with h22206 | h22206
                                    · linarith only [h20411, h22206, hlam]
                                    · linarith only [h20420, h22206, hlam]
                                · linarith only [h20414, h22203, hlam]
                              · linarith only [h20408, h22202, hlam]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h20420, h21506, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22095_1, p22199_1]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h14396, h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22199_1]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p22199_1]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              rcases p22199_3 (m.d 0 3) (by simp) with h22215 | h22215
                              · linarith only [h14396, h22215, hlam]
                              · linarith only [h20408, h22215, hlam]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h20414, h20420, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22095_1, p22199_1]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22199_1]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h20408, hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h20414, hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h20420, hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h21506, hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h20411, hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h20417, hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h20411, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22199_1]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h14396, h20411, h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22199_1]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h20412, hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h20418, hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [hc23, hc35, hlam, hphi, p22199_1]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [h21784, hlam, p22199_0]
                            · have p22199_0 := h22199c.1
                              have p22199_1 := h22199c.2.1
                              have p22199_2 := h22199c.2.2.1
                              have p22199_3 := h22199c.2.2.2
                              linarith only [hlam, p22199_0]
                        · linarith only [h21783, h22196, hlam]
                    · linarith only [h20416, h22193, hlam]
                  · linarith only [h20410, h22192, hlam]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [h20410, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [h20416, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  rcases p22095_3 (m.d 0 2) (by simp) with h22240 | h22240
                  · rcases p22095_3 (m.d 1 2) (by simp) with h22241 | h22241
                    · rcases p22095_3 (m.d 2 3) (by simp) with h22242 | h22242
                      · linarith only [h21506, h22242, hlam]
                      · rcases p22095_3 (m.d 2 4) (by simp) with h22244 | h22244
                        · rcases p22095_3 (m.d 2 5) (by simp) with h22245 | h22245
                          · rcases h3bigk with h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c | h22246c
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h14396, hlam, p22246_1]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              rcases p22246_3 (m.d 0 3) (by simp) with h22249 | h22249
                              · rcases p22246_3 (m.d 1 3) (by simp) with h22250 | h22250
                                · rcases p22246_3 (m.d 2 3) (by simp) with h22251 | h22251
                                  · linarith only [h20408, h22251, hlam]
                                  · rcases p22246_3 (m.d 3 4) (by simp) with h22253 | h22253
                                    · linarith only [h20411, h22253, hlam]
                                    · linarith only [h20420, h22253, hlam]
                                · linarith only [h20414, h22250, hlam]
                              · linarith only [h20408, h22249, hlam]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h14396, h20414, h20420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22246_1]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h14396, h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22246_1]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h14396, h20414, hc01, hc12, hlam, hphi, p22246_1]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              rcases p22246_3 (m.d 0 3) (by simp) with h22262 | h22262
                              · linarith only [h14396, h22262, hlam]
                              · linarith only [h20408, h22262, hlam]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h20414, h20420, h21783, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22095_1, p22246_1]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22095_1, p22246_1]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h20408, hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h20414, hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h20420, hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h21506, hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h20411, hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h20417, hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h20411, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p22246_1]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h14396, h20411, h20414, h21506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p22095_1, p22246_1]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h20412, hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h20418, hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [hc23, hc35, hlam, hphi, p22246_1]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [h21784, hlam, p22246_0]
                            · have p22246_0 := h22246c.1
                              have p22246_1 := h22246c.2.1
                              have p22246_2 := h22246c.2.2.1
                              have p22246_3 := h22246c.2.2.2
                              linarith only [hlam, p22246_0]
                          · linarith only [h21506, h22245, hlam]
                        · linarith only [h20420, h22244, hlam]
                    · linarith only [h20414, h22241, hlam]
                  · linarith only [h20408, h22240, hlam]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [h21783, hlam, p22095_0]
                · have p22095_0 := h22095c.1
                  have p22095_1 := h22095c.2.1
                  have p22095_2 := h22095c.2.2.1
                  have p22095_3 := h22095c.2.2.2
                  linarith only [hlam, p22095_0]
              · linarith only [h18815, h22094, hlam]
            · linarith only [h16915, h22093, hlam]
          · linarith only [h14396, h22092, hlam]
        · linarith only [h0, h22091, hlam]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [h20410, hlam, p21785_1]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [h20412, hlam, p21785_0]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [h20413, hlam, p21785_1]
    · have p21785_0 := h21785c.1
      have p21785_1 := h21785c.2.1
      have p21785_2 := h21785c.2.2.1
      have p21785_3 := h21785c.2.2.2
      linarith only [hlam, p21785_0]
  · linarith only [h20420, h21783, h21784, hlam]

end R2N4
