import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h822 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h823 | h823
  · rcases m.htr 0 3 5 (by decide) (by decide) with h824 | h824
    · rcases m.htr 0 4 5 (by decide) (by decide) with h825 | h825
      · rcases m.htr 1 2 3 (by decide) (by decide) with h826 | h826
        · linarith only [h0, h4, h822, h826, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h828 | h828
          · rcases m.htr 1 2 5 (by decide) (by decide) with h829 | h829
            · rcases m.htr 1 3 4 (by decide) (by decide) with h830 | h830
              · rcases m.htr 1 3 5 (by decide) (by decide) with h831 | h831
                · rcases m.htr 1 4 5 (by decide) (by decide) with h832 | h832
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h833 | h833
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h834 | h834
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h835 | h835
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h836 | h836
                          · rcases h1bigk with h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c | h837c
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h828, h833, h836, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p837_1, u3ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h830, h836, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p837_1, u3ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              rcases p837_3 (m.d 0 1) (by simp) with h841 | h841
                              · rcases p837_3 (m.d 1 2) (by simp) with h842 | h842
                                · linarith only [h0, h842, hlam]
                                · linarith only [h828, h842, hlam]
                              · linarith only [h841, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              rcases p837_3 (m.d 0 1) (by simp) with h846 | h846
                              · rcases p837_3 (m.d 1 2) (by simp) with h847 | h847
                                · linarith only [h0, h847, hlam]
                                · linarith only [h829, h847, hlam]
                              · linarith only [h846, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h0, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h826, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h0, h4, h828, h833, h836, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p837_1, u3ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h0, h4, h831, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p837_1, u3ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h1, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h1, h828, h833, h836, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p837_1, u3ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h1, h828, h833, h836, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p837_1, u3ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h1, h831, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p837_1, u3ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h2, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h828, hlam, p837_1]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h830, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h2, h831, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p837_1, u3ehi4]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h3, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h829, hlam, p837_1]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h831, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [h832, hlam, p837_0]
                            · have p837_0 := h837c.1
                              have p837_1 := h837c.2.1
                              have p837_2 := h837c.2.2.1
                              have p837_3 := h837c.2.2.2
                              linarith only [hlam, p837_0]
                          · linarith only [h0, h4, h828, h832, h836, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h4, h828, h832, h833, h835, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h4, h823, h834, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h0, h4, h828, h830, h833, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h875 | h875
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h876 | h876
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h877 | h877
                        · linarith only [h828, h832, h877, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h879 | h879
                          · linarith only [h828, h832, h875, h879, hlam]
                          · rcases h1bigk with h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c | h881c
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h828, h875, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p881_1, u3ehi3]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h826, h828, h875, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p881_1, u3ehi3]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              rcases p881_3 (m.d 0 1) (by simp) with h885 | h885
                              · rcases p881_3 (m.d 1 2) (by simp) with h886 | h886
                                · linarith only [h0, h886, hlam]
                                · linarith only [h828, h886, hlam]
                              · linarith only [h885, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              rcases p881_3 (m.d 0 1) (by simp) with h890 | h890
                              · rcases p881_3 (m.d 1 2) (by simp) with h891 | h891
                                · linarith only [h0, h891, hlam]
                                · linarith only [h829, h891, hlam]
                              · linarith only [h890, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h0, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h826, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h0, h828, h875, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p881_1, u3ehi3]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h0, h4, h828, h832, h875, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p881_1, u3ehi3]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h1, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h1, h828, h875, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p881_1, u3ehi3]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h1, h828, h875, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p881_1, u3ehi3]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h1, h828, h832, h875, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p881_1, u3ehi3]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h2, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h828, hlam, p881_1]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h830, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h832, hlam, p881_1]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h3, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h829, hlam, p881_1]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h831, hlam, p881_0]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [h3, h828, h875, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p881_1, u3ehi3]
                            · have p881_0 := h881c.1
                              have p881_1 := h881c.2.1
                              have p881_2 := h881c.2.2.1
                              have p881_3 := h881c.2.2.2
                              linarith only [hlam, p881_0]
                      · linarith only [h4, h823, h876, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h4, h823, h825, h830, h832, h875, hlam]
                · linarith only [h4, h822, h824, h830, h831, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h826, h828, h830, hlam]
            · linarith only [h4, h822, h829, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h920 | h920
            · rcases m.htr 1 3 4 (by decide) (by decide) with h921 | h921
              · rcases m.htr 1 3 5 (by decide) (by decide) with h922 | h922
                · rcases m.htr 1 4 5 (by decide) (by decide) with h923 | h923
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h924 | h924
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h925 | h925
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h926 | h926
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h927 | h927
                          · rcases h1bigk with h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h920, h925, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u3ehi4]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h828, h920, h921, h925, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u3ehi4]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h828, h920, h925, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u3ehi4]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              rcases p928_3 (m.d 0 1) (by simp) with h933 | h933
                              · rcases p928_3 (m.d 1 2) (by simp) with h934 | h934
                                · linarith only [h0, h934, hlam]
                                · linarith only [h920, h934, hlam]
                              · linarith only [h933, hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h0, hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h826, hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h828, hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h828, h920, h925, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p928_1, u3ehi4]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h1, hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h1, h920, h925, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u3ehi4]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h1, h828, h920, h925, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u3ehi4]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h1, h920, h925, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u3ehi4]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h2, hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h920, h925, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p928_1, u3ehi4]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h921, hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h1, h920, h921, h925, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p928_1, u3ehi4]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h3, hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h920, hlam, p928_1]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h922, hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [h923, hlam, p928_0]
                            · have p928_0 := h928c.1
                              have p928_1 := h928c.2.1
                              have p928_2 := h928c.2.2.1
                              have p928_3 := h928c.2.2.2
                              linarith only [hlam, p928_0]
                          · linarith only [h1, h921, h923, h927, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h828, h920, h923, h925, h926, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h4, h823, h925, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1, h4, h921, h924, hlam]
                  · linarith only [h828, h920, h923, hlam]
                · linarith only [h4, h822, h824, h921, h922, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h964 | h964
                · linarith only [h823, h921, h964, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h826, h920, h964, hlam]
            · linarith only [h4, h822, h920, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h968 | h968
        · linarith only [h0, h4, h822, h968, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h970 | h970
          · rcases m.htr 1 2 5 (by decide) (by decide) with h971 | h971
            · rcases m.htr 1 3 4 (by decide) (by decide) with h972 | h972
              · rcases m.htr 1 3 5 (by decide) (by decide) with h973 | h973
                · rcases m.htr 1 4 5 (by decide) (by decide) with h974 | h974
                  · linarith only [h2, h825, h974, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h976 | h976
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h977 | h977
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h978 | h978
                        · linarith only [h2, h825, h970, h978, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h980 | h980
                          · linarith only [h2, h825, h970, h976, h980, hlam]
                          · rcases h1bigk with h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c | h982c
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h971, h976, h978, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p982_1, u3ehi3]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h968, h971, h976, h978, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p982_1, u3ehi3]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              rcases p982_3 (m.d 0 1) (by simp) with h986 | h986
                              · rcases p982_3 (m.d 1 2) (by simp) with h987 | h987
                                · linarith only [h0, h987, hlam]
                                · linarith only [h970, h987, hlam]
                              · linarith only [h986, hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              rcases p982_3 (m.d 0 1) (by simp) with h991 | h991
                              · rcases p982_3 (m.d 1 2) (by simp) with h992 | h992
                                · linarith only [h0, h992, hlam]
                                · linarith only [h971, h992, hlam]
                              · linarith only [h991, hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h0, hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h968, hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h0, h4, h970, h976, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p982_1, u3ehi3]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h0, h4, h970, h974, h976, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p982_1, u3ehi3]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h1, hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h1, h970, h976, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p982_1, u3ehi3]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h1, h970, h976, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p982_1, u3ehi3]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h1, h970, h974, h976, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p982_1, u3ehi3]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h2, hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h970, hlam, p982_1]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h972, hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h974, hlam, p982_1]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h3, hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h971, hlam, p982_1]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h973, hlam, p982_0]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [h3, h970, h976, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p982_1, u3ehi3]
                            · have p982_0 := h982c.1
                              have p982_1 := h982c.2.1
                              have p982_2 := h982c.2.2.1
                              have p982_3 := h982c.2.2.2
                              linarith only [hlam, p982_0]
                      · linarith only [h4, h823, h977, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h2, h4, h822, h825, h972, h976, hlam]
                · linarith only [h972, h973, hc35, hlam, hphi, u3ehi3]
              · linarith only [h823, h825, h972, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h4, h822, h971, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1021 | h1021
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1022 | h1022
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1023 | h1023
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1024 | h1024
                  · linarith only [h1024, h2, h825, hlam]
                  · linarith only [h1021, h1024, h970, hlam]
                · linarith only [h1022, h1023, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1022, h823, h825, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h1021, h4, h822, hc12, hc23, hlam, hphi]
    · linarith only [h823, h824, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1031 | h1031
    · linarith only [h1031, h823, hc34, hlam, hphi, u3ehi4]
    · linarith only [h1031, h4, h822, hlam]

end R2N4
