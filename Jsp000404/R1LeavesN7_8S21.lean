import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11598000 in
set_option maxHeartbeats 11598000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h9886 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14268 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h14663 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h14791 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  rcases m.htr 0 3 5 (by decide) (by decide) with h14792 | h14792
  · rcases m.htr 0 4 5 (by decide) (by decide) with h14793 | h14793
    · rcases m.htr 1 2 3 (by decide) (by decide) with h14794 | h14794
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14795 | h14795
        · rcases m.htr 1 2 5 (by decide) (by decide) with h14796 | h14796
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14797 | h14797
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14798 | h14798
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14799 | h14799
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14800 | h14800
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14801 | h14801
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14802 | h14802
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14803 | h14803
                        · linarith only [h14791, h14794, h14803, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases h0bigk with h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [hlam, p14805_0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h0, hlam, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h7600, hlam, p14805_0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h8836, hlam, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h9666, hlam, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14663, h14794, h14800, h14802, hc01, hc12, hlam, hphi, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [hlam, p14805_0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h9886, hlam, p14805_0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14268, hlam, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14663, hlam, p14805_0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14794, h9886, hc01, hc12, hlam, hphi, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h0, h14794, h9886, hc01, hc12, hlam, hphi, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [hlam, p14805_0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14793, h14794, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p14805_1, u5ehi0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14794, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p14805_1, u5ehi0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14268, h14794, h14800, hc01, hc12, hlam, hphi, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h0, h14268, h14794, h14800, hc01, hc12, hlam, hphi, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14791, hlam, p14805_0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [hlam, p14805_0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14268, h14794, h14800, hc12, hlam, hphi, ht01, ht0b, ht5b, p14805_1, u5ehi0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14663, h14794, h14800, h14802, hc01, hc12, hlam, hphi, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h0, h14663, h14794, h14800, h14802, hc01, hc12, hlam, hphi, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14792, hlam, p14805_0]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [h14793, hlam, p14805_1]
                          · have p14805_0 := h14805c.1
                            have p14805_1 := h14805c.2.1
                            have p14805_2 := h14805c.2.2.1
                            have p14805_3 := h14805c.2.2.2
                            linarith only [hlam, p14805_0]
                      · linarith only [h14268, h14793, h14802, hlam]
                    · linarith only [h14792, h14801, h9886, hlam]
                  · linarith only [h14791, h14800, h9886, hlam]
                · linarith only [h14791, h14793, h14799, h8836, h9886, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h14792, h14794, h14798, h7600, h9886, hc01, hc12, hlam, hphi]
            · linarith only [h14791, h14794, h14797, h9886, hlam]
          · linarith only [h14792, h14794, h14796, h9886, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
        · linarith only [h14791, h14793, h14794, h14795, h9886, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14839 | h14839
        · linarith only [h14268, h14793, h14794, h14839, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h14841 | h14841
          · linarith only [h0, h14663, h14794, h14841, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14843 | h14843
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14844 | h14844
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14845 | h14845
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14846 | h14846
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14847 | h14847
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14848 | h14848
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14849 | h14849
                        · rcases h0bigk with h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c | h14850c
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [hlam, p14850_0]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h0, hlam, p14850_1]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h7600, hlam, p14850_0]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h8836, hlam, p14850_1]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h9666, hlam, p14850_1]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h0, h14841, h14846, h14848, hc01, hc23, hlam, hphi, ht12, p14850_1]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [hlam, p14850_0]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h9886, hlam, p14850_0]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h14268, hlam, p14850_1]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h14663, hlam, p14850_0]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            rcases p14850_3 (m.d 0 1) (by simp) with h14861 | h14861
                            · linarith only [h14861, h7600, hlam]
                            · rcases p14850_3 (m.d 0 2) (by simp) with h14863 | h14863
                              · linarith only [h14863, h9886, hlam]
                              · linarith only [h0, h14863, hlam]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            rcases p14850_3 (m.d 0 1) (by simp) with h14866 | h14866
                            · linarith only [h14866, h7600, hlam]
                            · rcases p14850_3 (m.d 0 2) (by simp) with h14868 | h14868
                              · linarith only [h14868, h9886, hlam]
                              · rcases p14850_3 (m.d 0 3) (by simp) with h14870 | h14870
                                · rcases p14850_3 (m.d 0 4) (by simp) with h14871 | h14871
                                  · linarith only [h14791, h14871, hlam]
                                  · linarith only [h14268, h14871, hlam]
                                · linarith only [h14870, h9886, hlam]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [hlam, p14850_0]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h14791, h14849, hc03, hlam, hphi, ht0b, ht5b, p14850_1, u5ehi4]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            rcases p14850_3 (m.d 0 1) (by simp) with h14877 | h14877
                            · linarith only [h14877, h7600, hlam]
                            · rcases p14850_3 (m.d 0 2) (by simp) with h14879 | h14879
                              · linarith only [h14879, h9886, hlam]
                              · rcases p14850_3 (m.d 0 3) (by simp) with h14881 | h14881
                                · rcases p14850_3 (m.d 0 4) (by simp) with h14882 | h14882
                                  · linarith only [h14791, h14882, hlam]
                                  · linarith only [h14793, h14882, hlam]
                                · linarith only [h14792, h14881, hlam]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            rcases p14850_3 (m.d 0 1) (by simp) with h14886 | h14886
                            · linarith only [h14886, h8836, hlam]
                            · rcases p14850_3 (m.d 0 2) (by simp) with h14888 | h14888
                              · linarith only [h14268, h14888, hlam]
                              · linarith only [h0, h14888, hlam]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            rcases p14850_3 (m.d 0 1) (by simp) with h14891 | h14891
                            · linarith only [h14891, h8836, hlam]
                            · rcases p14850_3 (m.d 0 2) (by simp) with h14893 | h14893
                              · linarith only [h14268, h14893, hlam]
                              · rcases p14850_3 (m.d 0 3) (by simp) with h14895 | h14895
                                · rcases p14850_3 (m.d 0 4) (by simp) with h14896 | h14896
                                  · rcases p14850_3 (m.d 0 5) (by simp) with h14897 | h14897
                                    · linarith only [h14793, h14897, hlam]
                                    · linarith only [h14663, h14897, hlam]
                                  · linarith only [h14268, h14896, hlam]
                                · linarith only [h14895, h9886, hlam]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h14791, hlam, p14850_0]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [hlam, p14850_0]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            rcases p14850_3 (m.d 0 1) (by simp) with h14904 | h14904
                            · linarith only [h14904, h8836, hlam]
                            · rcases p14850_3 (m.d 0 2) (by simp) with h14906 | h14906
                              · linarith only [h14268, h14906, hlam]
                              · rcases p14850_3 (m.d 0 3) (by simp) with h14908 | h14908
                                · rcases p14850_3 (m.d 0 4) (by simp) with h14909 | h14909
                                  · rcases p14850_3 (m.d 0 5) (by simp) with h14910 | h14910
                                    · linarith only [h14793, h14910, hlam]
                                    · rcases h2bigk with h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c | h14912c
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [hlam, p14912_0]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h0, hlam, p14912_1]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h9886, hlam, p14912_0]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h14268, hlam, p14912_0]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h14663, hlam, p14912_0]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h0, h14841, h14846, h14848, hc01, hc23, hlam, hphi, ht12, p14912_1]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [hlam, p14912_0]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h14794, hlam, p14912_0]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h14839, hlam, p14912_0]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h14841, hlam, p14912_0]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        rcases p14912_3 (m.d 0 2) (by simp) with h14923 | h14923
                                        · linarith only [h14923, hlam, p14912_0]
                                        · rcases p14912_3 (m.d 1 2) (by simp) with h14925 | h14925
                                          · linarith only [h14794, h14925, hlam]
                                          · linarith only [h0, h14925, hlam]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p14912_1]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [hlam, p14912_0]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h0, h14268, hc01, hc23, hlam, hphi, ht12, p14912_1]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h0, h14663, hc01, hc23, hlam, hphi, ht12, p14912_1]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        rcases p14912_3 (m.d 0 2) (by simp) with h14932 | h14932
                                        · linarith only [h14932, hlam, p14912_0]
                                        · rcases p14912_3 (m.d 1 2) (by simp) with h14934 | h14934
                                          · linarith only [h14839, h14934, hlam]
                                          · linarith only [h0, h14934, hlam]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p14912_1]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h14846, hlam, p14912_1]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [hlam, p14912_0]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h0, h14841, h14846, hc01, hc23, hlam, hphi, ht12, p14912_1]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        rcases p14912_3 (m.d 0 2) (by simp) with h14941 | h14941
                                        · linarith only [h14941, hlam, p14912_0]
                                        · rcases p14912_3 (m.d 1 2) (by simp) with h14943 | h14943
                                          · linarith only [h14841, h14943, hlam]
                                          · linarith only [h0, h14943, hlam]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p14912_1]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h14847, hlam, p14912_1]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [h14848, hlam, p14912_0]
                                      · have p14912_0 := h14912c.1
                                        have p14912_1 := h14912c.2.1
                                        have p14912_2 := h14912c.2.2.1
                                        have p14912_3 := h14912c.2.2.2
                                        linarith only [hlam, p14912_0]
                                  · linarith only [h14793, h14909, hlam]
                                · linarith only [h14792, h14908, hlam]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            rcases p14850_3 (m.d 0 1) (by simp) with h14952 | h14952
                            · linarith only [h14952, h9666, hlam]
                            · rcases p14850_3 (m.d 0 2) (by simp) with h14954 | h14954
                              · linarith only [h14663, h14954, hlam]
                              · linarith only [h0, h14954, hlam]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            rcases p14850_3 (m.d 0 1) (by simp) with h14957 | h14957
                            · linarith only [h14957, h9666, hlam]
                            · rcases p14850_3 (m.d 0 2) (by simp) with h14959 | h14959
                              · linarith only [h14663, h14959, hlam]
                              · rcases p14850_3 (m.d 0 3) (by simp) with h14961 | h14961
                                · rcases p14850_3 (m.d 0 4) (by simp) with h14962 | h14962
                                  · rcases p14850_3 (m.d 0 5) (by simp) with h14963 | h14963
                                    · rcases h2bigk with h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c | h14964c
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [hlam, p14964_0]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h0, hlam, p14964_1]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h9886, hlam, p14964_0]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h14268, hlam, p14964_0]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h14663, hlam, p14964_0]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h0, h14794, hc01, hc23, hlam, hphi, ht12, p14964_1]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [hlam, p14964_0]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h14794, hlam, p14964_0]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h14839, hlam, p14964_0]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h14841, hlam, p14964_0]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        rcases p14964_3 (m.d 0 2) (by simp) with h14975 | h14975
                                        · linarith only [h14975, hlam, p14964_0]
                                        · rcases p14964_3 (m.d 1 2) (by simp) with h14977 | h14977
                                          · linarith only [h14794, h14977, hlam]
                                          · linarith only [h0, h14977, hlam]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p14964_1]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [hlam, p14964_0]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h14839, h8836, hc01, hc23, hlam, hphi, ht12, p14964_1]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h0, h14841, h9666, hc01, hc23, hlam, hphi, ht12, p14850_1, p14964_1]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        rcases p14964_3 (m.d 0 2) (by simp) with h14984 | h14984
                                        · linarith only [h14984, hlam, p14964_0]
                                        · rcases p14964_3 (m.d 1 2) (by simp) with h14986 | h14986
                                          · linarith only [h14839, h14986, hlam]
                                          · linarith only [h0, h14986, hlam]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p14964_1]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h14846, hlam, p14964_1]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [hlam, p14964_0]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h0, h14841, h14846, h9666, hc01, hc23, hlam, hphi, ht12, p14850_1, p14964_1]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        rcases p14964_3 (m.d 0 2) (by simp) with h14993 | h14993
                                        · linarith only [h14993, hlam, p14964_0]
                                        · rcases p14964_3 (m.d 1 2) (by simp) with h14995 | h14995
                                          · linarith only [h14841, h14995, hlam]
                                          · linarith only [h0, h14995, hlam]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p14964_1]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h14847, hlam, p14964_1]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [h14848, hlam, p14964_0]
                                      · have p14964_0 := h14964c.1
                                        have p14964_1 := h14964c.2.1
                                        have p14964_2 := h14964c.2.2.1
                                        have p14964_3 := h14964c.2.2.2
                                        linarith only [hlam, p14964_0]
                                    · linarith only [h14663, h14963, hlam]
                                  · linarith only [h14268, h14962, hlam]
                                · linarith only [h14961, h9886, hlam]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h14792, hlam, p14850_0]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [h14793, hlam, p14850_1]
                          · have p14850_0 := h14850c.1
                            have p14850_1 := h14850c.2.1
                            have p14850_2 := h14850c.2.2.1
                            have p14850_3 := h14850c.2.2.2
                            linarith only [hlam, p14850_0]
                        · rcases h0bigk with h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c | h15008c
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [hlam, p15008_0]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h0, hlam, p15008_1]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h7600, hlam, p15008_0]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h8836, hlam, p15008_1]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h9666, hlam, p15008_1]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h9886, hc01, hc23, hlam, hphi, ht12, p15008_1]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [hlam, p15008_0]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h9886, hlam, p15008_0]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h14268, hlam, p15008_1]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h14663, hlam, p15008_0]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            rcases p15008_3 (m.d 0 1) (by simp) with h15019 | h15019
                            · linarith only [h15019, h7600, hlam]
                            · rcases p15008_3 (m.d 0 2) (by simp) with h15021 | h15021
                              · linarith only [h15021, h9886, hlam]
                              · linarith only [h0, h15021, hlam]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            rcases p15008_3 (m.d 0 1) (by simp) with h15024 | h15024
                            · linarith only [h15024, h7600, hlam]
                            · rcases p15008_3 (m.d 0 2) (by simp) with h15026 | h15026
                              · linarith only [h15026, h9886, hlam]
                              · rcases p15008_3 (m.d 0 3) (by simp) with h15028 | h15028
                                · rcases p15008_3 (m.d 0 4) (by simp) with h15029 | h15029
                                  · linarith only [h14791, h15029, hlam]
                                  · linarith only [h14268, h15029, hlam]
                                · linarith only [h15028, h9886, hlam]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [hlam, p15008_0]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h14793, h14794, h14849, h7600, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15008_1]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            rcases p15008_3 (m.d 0 1) (by simp) with h15035 | h15035
                            · linarith only [h15035, h7600, hlam]
                            · rcases p15008_3 (m.d 0 2) (by simp) with h15037 | h15037
                              · linarith only [h15037, h9886, hlam]
                              · rcases p15008_3 (m.d 0 3) (by simp) with h15039 | h15039
                                · rcases p15008_3 (m.d 0 4) (by simp) with h15040 | h15040
                                  · linarith only [h14791, h15040, hlam]
                                  · linarith only [h14793, h15040, hlam]
                                · linarith only [h14792, h15039, hlam]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            rcases p15008_3 (m.d 0 1) (by simp) with h15044 | h15044
                            · linarith only [h15044, h8836, hlam]
                            · rcases p15008_3 (m.d 0 2) (by simp) with h15046 | h15046
                              · linarith only [h14268, h15046, hlam]
                              · linarith only [h0, h15046, hlam]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            rcases p15008_3 (m.d 0 1) (by simp) with h15049 | h15049
                            · linarith only [h15049, h8836, hlam]
                            · rcases p15008_3 (m.d 0 2) (by simp) with h15051 | h15051
                              · linarith only [h14268, h15051, hlam]
                              · rcases p15008_3 (m.d 0 3) (by simp) with h15053 | h15053
                                · rcases p15008_3 (m.d 0 4) (by simp) with h15054 | h15054
                                  · rcases p15008_3 (m.d 0 5) (by simp) with h15055 | h15055
                                    · linarith only [h14793, h15055, hlam]
                                    · linarith only [h14663, h15055, hlam]
                                  · linarith only [h14268, h15054, hlam]
                                · linarith only [h15053, h9886, hlam]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h14791, hlam, p15008_0]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [hlam, p15008_0]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            rcases p15008_3 (m.d 0 1) (by simp) with h15062 | h15062
                            · linarith only [h15062, h8836, hlam]
                            · rcases p15008_3 (m.d 0 2) (by simp) with h15064 | h15064
                              · linarith only [h14268, h15064, hlam]
                              · rcases p15008_3 (m.d 0 3) (by simp) with h15066 | h15066
                                · rcases p15008_3 (m.d 0 4) (by simp) with h15067 | h15067
                                  · rcases p15008_3 (m.d 0 5) (by simp) with h15068 | h15068
                                    · linarith only [h14793, h15068, hlam]
                                    · rcases h2bigk with h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c | h15070c
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [hlam, p15070_0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h0, hlam, p15070_1]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h9886, hlam, p15070_0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h14268, hlam, p15070_0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h14663, hlam, p15070_0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h14841, h14846, h14848, hc02, hc23, hlam, hphi, p15070_1]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [hlam, p15070_0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h14794, hlam, p15070_0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h14839, hlam, p15070_0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h14841, hlam, p15070_0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        rcases p15070_3 (m.d 0 2) (by simp) with h15081 | h15081
                                        · linarith only [h15081, hlam, p15070_0]
                                        · rcases p15070_3 (m.d 1 2) (by simp) with h15083 | h15083
                                          · linarith only [h14794, h15083, hlam]
                                          · linarith only [h0, h15083, hlam]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p15070_1]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [hlam, p15070_0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h14839, h8836, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p15008_1, p15070_1, u5ehi0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h0, h14663, hc01, hc23, hlam, hphi, ht12, p15070_1]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        rcases p15070_3 (m.d 0 2) (by simp) with h15090 | h15090
                                        · linarith only [h15090, hlam, p15070_0]
                                        · rcases p15070_3 (m.d 1 2) (by simp) with h15092 | h15092
                                          · linarith only [h14839, h15092, hlam]
                                          · linarith only [h0, h15092, hlam]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p15070_1]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h14846, hlam, p15070_1]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [hlam, p15070_0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h0, h14841, h14846, hc01, hc23, hlam, hphi, ht12, p15070_1]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        rcases p15070_3 (m.d 0 2) (by simp) with h15099 | h15099
                                        · linarith only [h15099, hlam, p15070_0]
                                        · rcases p15070_3 (m.d 1 2) (by simp) with h15101 | h15101
                                          · linarith only [h14841, h15101, hlam]
                                          · linarith only [h0, h15101, hlam]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p15070_1]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h14847, hlam, p15070_1]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [h14848, hlam, p15070_0]
                                      · have p15070_0 := h15070c.1
                                        have p15070_1 := h15070c.2.1
                                        have p15070_2 := h15070c.2.2.1
                                        have p15070_3 := h15070c.2.2.2
                                        linarith only [hlam, p15070_0]
                                  · linarith only [h14793, h15067, hlam]
                                · linarith only [h14792, h15066, hlam]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            rcases p15008_3 (m.d 0 1) (by simp) with h15110 | h15110
                            · linarith only [h15110, h9666, hlam]
                            · rcases p15008_3 (m.d 0 2) (by simp) with h15112 | h15112
                              · linarith only [h14663, h15112, hlam]
                              · linarith only [h0, h15112, hlam]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            rcases p15008_3 (m.d 0 1) (by simp) with h15115 | h15115
                            · linarith only [h15115, h9666, hlam]
                            · rcases p15008_3 (m.d 0 2) (by simp) with h15117 | h15117
                              · linarith only [h14663, h15117, hlam]
                              · rcases p15008_3 (m.d 0 3) (by simp) with h15119 | h15119
                                · rcases p15008_3 (m.d 0 4) (by simp) with h15120 | h15120
                                  · rcases p15008_3 (m.d 0 5) (by simp) with h15121 | h15121
                                    · rcases h2bigk with h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c | h15122c
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [hlam, p15122_0]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h0, hlam, p15122_1]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h9886, hlam, p15122_0]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h14268, hlam, p15122_0]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h14663, hlam, p15122_0]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h0, h14794, hc01, hc23, hlam, hphi, ht12, p15122_1]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [hlam, p15122_0]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h14794, hlam, p15122_0]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h14839, hlam, p15122_0]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h14841, hlam, p15122_0]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        rcases p15122_3 (m.d 0 2) (by simp) with h15133 | h15133
                                        · linarith only [h15133, hlam, p15122_0]
                                        · rcases p15122_3 (m.d 1 2) (by simp) with h15135 | h15135
                                          · linarith only [h14794, h15135, hlam]
                                          · linarith only [h0, h15135, hlam]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p15122_1]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [hlam, p15122_0]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h14839, h8836, hc01, hc23, hlam, hphi, ht12, p15122_1]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h0, h14841, h9666, hc01, hc23, hlam, hphi, ht12, p15008_1, p15122_1]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        rcases p15122_3 (m.d 0 2) (by simp) with h15142 | h15142
                                        · linarith only [h15142, hlam, p15122_0]
                                        · rcases p15122_3 (m.d 1 2) (by simp) with h15144 | h15144
                                          · linarith only [h14839, h15144, hlam]
                                          · linarith only [h0, h15144, hlam]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p15122_1]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h14846, hlam, p15122_1]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [hlam, p15122_0]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h0, h14841, h14846, h9666, hc01, hc23, hlam, hphi, ht12, p15008_1, p15122_1]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        rcases p15122_3 (m.d 0 2) (by simp) with h15151 | h15151
                                        · linarith only [h15151, hlam, p15122_0]
                                        · rcases p15122_3 (m.d 1 2) (by simp) with h15153 | h15153
                                          · linarith only [h14841, h15153, hlam]
                                          · linarith only [h0, h15153, hlam]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p15122_1]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h14847, hlam, p15122_1]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [h14848, hlam, p15122_0]
                                      · have p15122_0 := h15122c.1
                                        have p15122_1 := h15122c.2.1
                                        have p15122_2 := h15122c.2.2.1
                                        have p15122_3 := h15122c.2.2.2
                                        linarith only [hlam, p15122_0]
                                    · linarith only [h14663, h15121, hlam]
                                  · linarith only [h14268, h15120, hlam]
                                · linarith only [h15119, h9886, hlam]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h14792, hlam, p15008_0]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [h14793, hlam, p15008_1]
                          · have p15008_0 := h15008c.1
                            have p15008_1 := h15008c.2.1
                            have p15008_2 := h15008c.2.2.1
                            have p15008_3 := h15008c.2.2.2
                            linarith only [hlam, p15008_0]
                      · linarith only [h14268, h14793, h14848, hlam]
                    · linarith only [h14792, h14794, h14847, h7600, hlam]
                  · linarith only [h0, h14794, h14846, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h14793, h14845, h8836, hlam]
              · linarith only [h14792, h14844, h7600, hlam]
            · linarith only [h14791, h14843, h7600, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15172 | h15172
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15173 | h15173
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15174 | h15174
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15175 | h15175
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15176 | h15176
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15177 | h15177
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15178 | h15178
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15179 | h15179
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15180 | h15180
                      · linarith only [h14793, h15173, h15180, h8836, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h14268, h15172, h15175, h15177, h15180, hc01, hc12, hlam, hphi]
                    · linarith only [h14792, h15179, h9886, hlam]
                  · linarith only [h14791, h15178, h9886, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15185 | h15185
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15186 | h15186
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15187 | h15187
                      · linarith only [h15173, h15177, h15187, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15189 | h15189
                        · linarith only [h14791, h15177, h15189, h8836, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases h0bigk with h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c | h15191c
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [hlam, p15191_0]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h0, hlam, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h7600, hlam, p15191_0]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h8836, hlam, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h9666, hlam, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h14268, h15173, hc01, hc14, hlam, hphi, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [hlam, p15191_0]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h9886, hlam, p15191_0]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h14268, hlam, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h14663, hlam, p15191_0]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h15172, h9886, hc01, hc12, hlam, hphi, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h0, h15172, h9886, hc01, hc12, hlam, hphi, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [hlam, p15191_0]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h15172, h8836, h9886, hc01, hc12, hlam, hphi, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h15172, h9886, hc12, hlam, hphi, ht01, ht0b, ht5b, p15191_1, u5ehi0]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h15177, h8836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h0, h14268, h15173, h15177, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h14791, hlam, p15191_0]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [hlam, p15191_0]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h14793, hlam, p15191_0]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h14663, h15172, h15186, hc01, hc12, hlam, hphi, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h0, h14663, h15172, h15186, hc01, hc12, hlam, hphi, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h14792, hlam, p15191_0]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [h14663, h15172, h15186, h8836, hc01, hc12, hlam, hphi, p15191_1]
                          · have p15191_0 := h15191c.1
                            have p15191_1 := h15191c.2.1
                            have p15191_2 := h15191c.2.2.1
                            have p15191_3 := h15191c.2.2.2
                            linarith only [hlam, p15191_0]
                    · linarith only [h14792, h15186, h9886, hlam]
                  · linarith only [h14791, h14792, h15177, h15185, h8836, h9886, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
              · linarith only [h14792, h15176, h7600, h9886, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h14791, h15172, h15175, h9886, hlam]
          · linarith only [h14792, h15172, h15174, h9886, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
        · linarith only [h14792, h15172, h15173, h9886, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15223 | h15223
        · linarith only [h0, h14268, h15172, h15223, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15225 | h15225
          · linarith only [h0, h14663, h15172, h15225, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15227 | h15227
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15228 | h15228
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15229 | h15229
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15230 | h15230
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15231 | h15231
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15232 | h15232
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15233 | h15233
                        · linarith only [h14791, h14793, h15233, hlam]
                        · rcases h0bigk with h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c | h15235c
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [hlam, p15235_0]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h0, hlam, p15235_1]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h7600, hlam, p15235_0]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h8836, hlam, p15235_1]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h9666, hlam, p15235_1]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h14268, h14793, h15227, h15229, hc01, hc13, hlam, hphi, p15235_1]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [hlam, p15235_0]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h9886, hlam, p15235_0]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h14268, hlam, p15235_1]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h14663, hlam, p15235_0]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            rcases p15235_3 (m.d 0 1) (by simp) with h15246 | h15246
                            · linarith only [h15246, h7600, hlam]
                            · rcases p15235_3 (m.d 0 2) (by simp) with h15248 | h15248
                              · linarith only [h15248, h9886, hlam]
                              · linarith only [h0, h15248, hlam]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            rcases p15235_3 (m.d 0 1) (by simp) with h15251 | h15251
                            · linarith only [h15251, h7600, hlam]
                            · rcases p15235_3 (m.d 0 2) (by simp) with h15253 | h15253
                              · linarith only [h15253, h9886, hlam]
                              · rcases p15235_3 (m.d 0 3) (by simp) with h15255 | h15255
                                · rcases p15235_3 (m.d 0 4) (by simp) with h15256 | h15256
                                  · linarith only [h14791, h15256, hlam]
                                  · linarith only [h14268, h15256, hlam]
                                · linarith only [h15255, h9886, hlam]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [hlam, p15235_0]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            rcases p15235_3 (m.d 0 1) (by simp) with h15261 | h15261
                            · linarith only [h15261, h7600, hlam]
                            · rcases p15235_3 (m.d 0 2) (by simp) with h15263 | h15263
                              · linarith only [h15263, h9886, hlam]
                              · rcases p15235_3 (m.d 0 3) (by simp) with h15265 | h15265
                                · rcases p15235_3 (m.d 0 4) (by simp) with h15266 | h15266
                                  · linarith only [h14791, h15266, hlam]
                                  · rcases p15235_3 (m.d 0 5) (by simp) with h15268 | h15268
                                    · linarith only [h14792, h15268, hlam]
                                    · linarith only [h14793, h15268, hlam]
                                · linarith only [h14791, h15265, hlam]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            rcases p15235_3 (m.d 0 1) (by simp) with h15272 | h15272
                            · linarith only [h15272, h7600, hlam]
                            · rcases p15235_3 (m.d 0 2) (by simp) with h15274 | h15274
                              · linarith only [h15274, h9886, hlam]
                              · rcases p15235_3 (m.d 0 3) (by simp) with h15276 | h15276
                                · rcases p15235_3 (m.d 0 4) (by simp) with h15277 | h15277
                                  · linarith only [h14791, h15277, hlam]
                                  · rcases p15235_3 (m.d 0 5) (by simp) with h15279 | h15279
                                    · linarith only [h14792, h15279, hlam]
                                    · rcases h2bigk with h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c | h15281c
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [hlam, p15281_0]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h0, hlam, p15281_1]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h9886, hlam, p15281_0]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h14268, hlam, p15281_0]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h14663, hlam, p15281_0]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h0, h15225, h15230, h15232, hc01, hc23, hlam, hphi, ht12, p15281_1]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [hlam, p15281_0]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h15172, hlam, p15281_0]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h15223, hlam, p15281_0]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h15225, hlam, p15281_0]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        rcases p15281_3 (m.d 0 2) (by simp) with h15292 | h15292
                                        · linarith only [h15292, hlam, p15281_0]
                                        · rcases p15281_3 (m.d 1 2) (by simp) with h15294 | h15294
                                          · linarith only [h15172, h15294, hlam]
                                          · linarith only [h0, h15294, hlam]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p15281_1]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [hlam, p15281_0]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h0, h14268, hc01, hc23, hlam, hphi, ht12, p15281_1]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h0, h15225, hc01, hc23, hlam, hphi, ht12, p15281_1]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        rcases p15281_3 (m.d 0 2) (by simp) with h15301 | h15301
                                        · linarith only [h15301, hlam, p15281_0]
                                        · rcases p15281_3 (m.d 1 2) (by simp) with h15303 | h15303
                                          · linarith only [h15223, h15303, hlam]
                                          · linarith only [h0, h15303, hlam]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h0, hc01, hc24, hlam, hphi, ht12, p15281_1]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h15230, hlam, p15281_1]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [hlam, p15281_0]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h0, h15225, h15230, hc01, hc23, hlam, hphi, ht12, p15281_1]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        rcases p15281_3 (m.d 0 2) (by simp) with h15310 | h15310
                                        · linarith only [h15310, hlam, p15281_0]
                                        · rcases p15281_3 (m.d 1 2) (by simp) with h15312 | h15312
                                          · linarith only [h15225, h15312, hlam]
                                          · linarith only [h0, h15312, hlam]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h0, hc01, hc25, hlam, hphi, ht12, p15281_1]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h15231, hlam, p15281_1]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [h15232, hlam, p15281_0]
                                      · have p15281_0 := h15281c.1
                                        have p15281_1 := h15281c.2.1
                                        have p15281_2 := h15281c.2.2.1
                                        have p15281_3 := h15281c.2.2.2
                                        linarith only [hlam, p15281_0]
                                · linarith only [h14792, h15276, hlam]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h14793, h15229, hc01, hc15, hlam, hphi, p15235_1]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h0, h14793, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15235_1]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h14791, hlam, p15235_0]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [hlam, p15235_0]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h14793, hlam, p15235_0]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h14793, h15172, h15227, h15229, hc01, hc23, hlam, hphi, ht12, p15235_1]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h0, h14793, h15172, h15227, h15229, hc01, hc23, hlam, hphi, ht12, p15235_1]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h14792, hlam, p15235_0]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [h14793, h15172, h15227, h15229, h8836, hc01, hc23, hlam, hphi, ht12, p15235_1]
                          · have p15235_0 := h15235c.1
                            have p15235_1 := h15235c.2.1
                            have p15235_2 := h15235c.2.2.1
                            have p15235_3 := h15235c.2.2.2
                            linarith only [hlam, p15235_0]
                      · linarith only [h0, h14268, h15172, h15227, h15229, h15232, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h14792, h14793, h15172, h15227, h15229, h15231, hlam]
                  · linarith only [h14791, h15172, h15227, h15230, h8836, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15333 | h15333
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15334 | h15334
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15335 | h15335
                      · linarith only [h15229, h15333, h15335, h8836, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h15223, h15335, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h14792, h15334, h9886, hlam]
                  · linarith only [h14791, h15172, h15333, h7600, hlam]
              · linarith only [h14792, h15228, h7600, hlam]
            · linarith only [h14791, h14792, h14793, h15227, h7600, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h15342 | h15342
    · linarith only [h14791, h14792, h15342, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h15344 | h15344
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15345 | h15345
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15346 | h15346
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15347 | h15347
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15348 | h15348
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15349 | h15349
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15350 | h15350
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15351 | h15351
                    · linarith only [h14791, h14792, h15344, h15351, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h15344, h15348, h15351, h9886, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h14791, h15344, h15350, h7600, h9886, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15355 | h15355
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15356 | h15356
                    · linarith only [h14791, h14792, h15344, h15356, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h15344, h15348, h15356, h9886, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h14791, h15344, h15355, h7600, h9886, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15360 | h15360
                · linarith only [h15342, h15347, h15348, h15360, h8836, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15362 | h15362
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15363 | h15363
                    · linarith only [h15344, h15348, h15363, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15365 | h15365
                      · linarith only [h15360, h15365, h8836, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15367 | h15367
                        · linarith only [h0, h14268, h14791, h15344, h15345, h15348, h15360, h15367, h9886, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases h0bigk with h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c | h15369c
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [hlam, p15369_0]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h0, hlam, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h7600, hlam, p15369_0]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h8836, hlam, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h9666, hlam, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h14268, h15345, hc01, hc14, hlam, hphi, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [hlam, p15369_0]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h9886, hlam, p15369_0]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h14268, hlam, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h14663, hlam, p15369_0]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h15344, h15348, h15367, h9886, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h15344, h15348, h15367, h9886, hc02, hc45, hlam, hphi, ht23, ht34, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [hlam, p15369_0]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h15344, h15348, h15367, h9886, hc04, hc45, hlam, hphi, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h14792, hlam, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h14791, h15344, h15348, h15367, h9886, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h0, h14791, h15344, h15348, h15367, h9886, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h14791, hlam, p15369_0]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [hlam, p15369_0]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h15342, hlam, p15369_0]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h14663, h15346, hc01, hc12, hlam, hphi, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h0, h14663, h15346, hc01, hc12, hlam, hphi, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h14791, h15348, h15367, h9666, hc34, hc45, hlam, hphi, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [h14663, h15346, h8836, hc01, hc12, hlam, hphi, p15369_1]
                          · have p15369_0 := h15369c.1
                            have p15369_1 := h15369c.2.1
                            have p15369_2 := h15369c.2.2.1
                            have p15369_3 := h15369c.2.2.2
                            linarith only [hlam, p15369_0]
                  · linarith only [h0, h14791, h15362, h7600, h9886, hc01, hc13, hlam, hphi]
            · linarith only [h14791, h15347, h7600, hlam]
          · linarith only [h0, h15344, h15346, h9886, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h15344, h15345, h9886, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h15399 | h15399
        · linarith only [h0, h14268, h15344, h15399, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15401 | h15401
          · linarith only [h0, h14663, h15344, h15401, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15403 | h15403
            · rcases m.htr 1 3 5 (by decide) (by decide) with h15404 | h15404
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15405 | h15405
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15406 | h15406
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15407 | h15407
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15408 | h15408
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15409 | h15409
                        · linarith only [h0, h14268, h14791, h14792, h15342, h15344, h15404, h15409, hc01, hc23, hlam, hphi, ht12]
                        · rcases h0bigk with h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c | h15411c
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [hlam, p15411_0]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h0, hlam, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h7600, hlam, p15411_0]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h8836, hlam, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h9666, hlam, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h9886, hc01, hc23, hlam, hphi, ht12, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [hlam, p15411_0]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h9886, hlam, p15411_0]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h14268, hlam, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h14663, hlam, p15411_0]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h14792, h15399, h15405, h15406, h15409, hc01, hc23, hlam, hphi, ht12, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h14792, h15399, h15405, h15406, h15409, hc02, hc23, hlam, hphi, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [hlam, p15411_0]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h0, h14268, h14792, h15399, h15405, h15406, h15409, hc01, hc23, hlam, hphi, ht12, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h14792, hlam, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h14791, h14792, h15399, h15405, h15406, h15409, hc01, hc23, hlam, hphi, ht12, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h0, h14791, h14792, h15399, h15405, h15406, h15409, hc01, hc23, hlam, hphi, ht12, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h14791, hlam, p15411_0]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [hlam, p15411_0]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h15342, hlam, p15411_0]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h14792, h15399, h15405, h15406, h15409, hc01, hc23, hlam, hphi, ht12, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h0, h14792, h15399, h15405, h15406, h15409, hc01, hc23, hlam, hphi, ht12, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h14791, h14792, h15399, h15405, h15406, h15409, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [h14792, h15399, h15405, h15406, h15409, h8836, hc01, hc23, hlam, hphi, ht12, p15411_1]
                          · have p15411_0 := h15411c.1
                            have p15411_1 := h15411c.2.1
                            have p15411_2 := h15411c.2.2.1
                            have p15411_3 := h15411c.2.2.2
                            linarith only [hlam, p15411_0]
                      · linarith only [h15399, h15405, h15408, hlam]
                    · linarith only [h0, h14268, h15342, h15399, h15405, h15406, h15407, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h14268, h14791, h15342, h15344, h15403, h15405, h15406, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15440 | h15440
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15441 | h15441
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15442 | h15442
                      · linarith only [h15405, h15442, h8836, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h15399, h15442, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h15344, h15404, h15441, hlam]
                  · linarith only [h14791, h14792, h15344, h15404, h15440, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15447 | h15447
                · linarith only [h0, h14268, h15342, h15403, h15404, h15447, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15449 | h15449
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15450 | h15450
                    · linarith only [h0, h15399, h15403, h15404, h15450, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h15344, h15450, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h14791, h15344, h15449, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · linarith only [h14791, h15403, h7600, hlam]

end R2N4
