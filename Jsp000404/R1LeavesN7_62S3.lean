import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_62S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3038000 in
set_option maxHeartbeats 3038000 in
theorem r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h772 | h772
  · rcases m.htr 0 3 5 (by decide) (by decide) with h773 | h773
    · rcases m.htr 0 4 5 (by decide) (by decide) with h774 | h774
      · rcases m.htr 1 2 3 (by decide) (by decide) with h775 | h775
        · linarith only [h0, h4, h775, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h777 | h777
          · rcases m.htr 1 3 4 (by decide) (by decide) with h778 | h778
            · rcases m.htr 1 3 5 (by decide) (by decide) with h779 | h779
              · rcases m.htr 1 4 5 (by decide) (by decide) with h780 | h780
                · rcases m.htr 2 3 4 (by decide) (by decide) with h781 | h781
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h782 | h782
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h783 | h783
                      · linarith only [h1, h778, h783, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases h3bigk with h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c | h785c
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht12, p785_1, u1ehi2]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h4, hlam, p785_1]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          rcases p785_3 (m.d 0 3) (by simp) with h789 | h789
                          · rcases p785_3 (m.d 1 3) (by simp) with h790 | h790
                            · linarith only [h1, h790, hlam]
                            · linarith only [h778, h790, hlam]
                          · linarith only [h789, hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          rcases p785_3 (m.d 0 3) (by simp) with h794 | h794
                          · rcases p785_3 (m.d 1 3) (by simp) with h795 | h795
                            · linarith only [h1, h795, hlam]
                            · linarith only [h779, h795, hlam]
                          · linarith only [h794, hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h1, hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h775, hlam, p785_1]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          rcases p785_3 (m.d 0 3) (by simp) with h802 | h802
                          · rcases p785_3 (m.d 1 3) (by simp) with h803 | h803
                            · rcases p785_3 (m.d 2 3) (by simp) with h804 | h804
                              · rcases p785_3 (m.d 3 4) (by simp) with h805 | h805
                                · linarith only [h805, hlam, p785_0]
                                · rcases p785_3 (m.d 3 5) (by simp) with h807 | h807
                                  · linarith only [h779, h807, hlam]
                                  · linarith only [h783, h807, hlam]
                              · linarith only [h781, h804, hlam]
                            · linarith only [h803, hlam, p785_0]
                          · linarith only [h772, h802, hlam]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p785_1, u5ehi3]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht12, p785_1, u1ehi2]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [hc23, hlam, hphi, ht12, p785_1, u1ehi2]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          rcases p785_3 (m.d 0 3) (by simp) with h817 | h817
                          · linarith only [h4, h817, hlam]
                          · linarith only [h772, h817, hlam]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          rcases p785_3 (m.d 0 3) (by simp) with h820 | h820
                          · linarith only [h4, h820, hlam]
                          · linarith only [h773, h820, hlam]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h772, hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h778, hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h781, hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h783, hlam, p785_1]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h773, hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h779, hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h782, hlam, p785_0]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [h0, h4, h777, h782, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p785_1]
                        · have p785_0 := h785c.1
                          have p785_1 := h785c.2.1
                          have p785_2 := h785c.2.2.1
                          have p785_3 := h785c.2.2.2
                          linarith only [hlam, p785_0]
                    · linarith only [h0, h4, h777, h779, h782, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h4, h777, h781, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h4, h772, h774, h780, hc23, hlam, hphi, ht12, u1ehi3]
              · linarith only [h4, h773, h779, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h4, h772, h775, h777, h778, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h838 | h838
            · rcases m.htr 1 3 5 (by decide) (by decide) with h839 | h839
              · rcases m.htr 1 4 5 (by decide) (by decide) with h840 | h840
                · rcases m.htr 2 3 4 (by decide) (by decide) with h841 | h841
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h842 | h842
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h843 | h843
                      · linarith only [h1, h838, h843, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases h3bigk with h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c | h845c
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht12, p845_1, u1ehi2]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h4, hlam, p845_1]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          rcases p845_3 (m.d 0 3) (by simp) with h849 | h849
                          · rcases p845_3 (m.d 1 3) (by simp) with h850 | h850
                            · linarith only [h1, h850, hlam]
                            · linarith only [h838, h850, hlam]
                          · linarith only [h849, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          rcases p845_3 (m.d 0 3) (by simp) with h854 | h854
                          · rcases p845_3 (m.d 1 3) (by simp) with h855 | h855
                            · linarith only [h1, h855, hlam]
                            · linarith only [h839, h855, hlam]
                          · linarith only [h854, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h1, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h775, hlam, p845_1]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          rcases p845_3 (m.d 0 3) (by simp) with h862 | h862
                          · rcases p845_3 (m.d 1 3) (by simp) with h863 | h863
                            · rcases p845_3 (m.d 2 3) (by simp) with h864 | h864
                              · rcases p845_3 (m.d 3 4) (by simp) with h865 | h865
                                · linarith only [h865, hlam, p845_0]
                                · rcases p845_3 (m.d 3 5) (by simp) with h867 | h867
                                  · linarith only [h839, h867, hlam]
                                  · linarith only [h843, h867, hlam]
                              · linarith only [h841, h864, hlam]
                            · linarith only [h863, hlam, p845_0]
                          · linarith only [h772, h862, hlam]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p845_1, u5ehi3]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht12, p845_1, u1ehi2]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [hc23, hlam, hphi, ht12, p845_1, u1ehi2]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          rcases p845_3 (m.d 0 3) (by simp) with h877 | h877
                          · linarith only [h4, h877, hlam]
                          · linarith only [h772, h877, hlam]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          rcases p845_3 (m.d 0 3) (by simp) with h880 | h880
                          · linarith only [h4, h880, hlam]
                          · linarith only [h773, h880, hlam]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h772, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h838, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h841, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h843, hlam, p845_1]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h773, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h839, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h842, hlam, p845_0]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [h1, h839, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p845_1]
                        · have p845_0 := h845c.1
                          have p845_1 := h845c.2.1
                          have p845_2 := h845c.2.2.1
                          have p845_3 := h845c.2.2.2
                          linarith only [hlam, p845_0]
                    · linarith only [h1, h4, h839, h842, hlam]
                  · linarith only [h0, h4, h841, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h4, h772, h774, h840, hc23, hlam, hphi, ht12, u1ehi3]
              · linarith only [h4, h773, h839, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h4, h772, h775, h838, hc23, hlam, hphi, ht12, u1ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h898 | h898
        · linarith only [h0, h4, h773, h898, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h900 | h900
          · rcases m.htr 1 3 4 (by decide) (by decide) with h901 | h901
            · rcases m.htr 1 3 5 (by decide) (by decide) with h902 | h902
              · rcases m.htr 1 4 5 (by decide) (by decide) with h903 | h903
                · linarith only [h2, h774, h903, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h905 | h905
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h906 | h906
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h907 | h907
                      · linarith only [h1, h774, h901, h907, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h3bigk with h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht12, p909_1, u1ehi2]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h4, hlam, p909_1]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          rcases p909_3 (m.d 0 3) (by simp) with h913 | h913
                          · rcases p909_3 (m.d 1 3) (by simp) with h914 | h914
                            · linarith only [h1, h914, hlam]
                            · linarith only [h901, h914, hlam]
                          · linarith only [h913, hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          rcases p909_3 (m.d 0 3) (by simp) with h918 | h918
                          · rcases p909_3 (m.d 1 3) (by simp) with h919 | h919
                            · linarith only [h1, h919, hlam]
                            · linarith only [h902, h919, hlam]
                          · linarith only [h918, hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h1, hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h898, hlam, p909_1]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          rcases p909_3 (m.d 0 3) (by simp) with h926 | h926
                          · rcases p909_3 (m.d 1 3) (by simp) with h927 | h927
                            · rcases p909_3 (m.d 2 3) (by simp) with h928 | h928
                              · rcases p909_3 (m.d 3 4) (by simp) with h929 | h929
                                · linarith only [h929, hlam, p909_0]
                                · rcases p909_3 (m.d 3 5) (by simp) with h931 | h931
                                  · linarith only [h902, h931, hlam]
                                  · linarith only [h907, h931, hlam]
                              · linarith only [h905, h928, hlam]
                            · linarith only [h927, hlam, p909_0]
                          · linarith only [h772, h926, hlam]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p909_1, u5ehi3]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht12, p909_1, u1ehi2]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [hc23, hlam, hphi, ht12, p909_1, u1ehi2]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          rcases p909_3 (m.d 0 3) (by simp) with h941 | h941
                          · linarith only [h4, h941, hlam]
                          · linarith only [h772, h941, hlam]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          rcases p909_3 (m.d 0 3) (by simp) with h944 | h944
                          · linarith only [h4, h944, hlam]
                          · linarith only [h773, h944, hlam]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h772, hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h901, hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h905, hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h907, hlam, p909_1]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h773, hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h902, hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h906, hlam, p909_0]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [h0, h4, h900, h906, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p909_1]
                        · have p909_0 := h909c.1
                          have p909_1 := h909c.2.1
                          have p909_2 := h909c.2.2.1
                          have p909_3 := h909c.2.2.2
                          linarith only [hlam, p909_0]
                    · linarith only [h0, h4, h900, h902, h906, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                  · linarith only [h0, h4, h900, h905, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
              · linarith only [h4, h773, h902, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h772, h774, h898, h900, h901, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h961 | h961
            · rcases m.htr 1 3 5 (by decide) (by decide) with h962 | h962
              · rcases m.htr 1 4 5 (by decide) (by decide) with h963 | h963
                · linarith only [h2, h774, h963, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h965 | h965
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h966 | h966
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h967 | h967
                      · linarith only [h2, h774, h961, h967, hc13, hlam, hphi, u1ehi3]
                      · rcases h3bigk with h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht12, p969_1, u1ehi2]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h4, hlam, p969_1]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          rcases p969_3 (m.d 0 3) (by simp) with h973 | h973
                          · rcases p969_3 (m.d 1 3) (by simp) with h974 | h974
                            · linarith only [h1, h974, hlam]
                            · linarith only [h961, h974, hlam]
                          · linarith only [h973, hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          rcases p969_3 (m.d 0 3) (by simp) with h978 | h978
                          · rcases p969_3 (m.d 1 3) (by simp) with h979 | h979
                            · linarith only [h1, h979, hlam]
                            · linarith only [h962, h979, hlam]
                          · linarith only [h978, hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h1, hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h898, hlam, p969_1]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          rcases p969_3 (m.d 0 3) (by simp) with h986 | h986
                          · rcases p969_3 (m.d 1 3) (by simp) with h987 | h987
                            · rcases p969_3 (m.d 2 3) (by simp) with h988 | h988
                              · rcases p969_3 (m.d 3 4) (by simp) with h989 | h989
                                · linarith only [h989, hlam, p969_0]
                                · rcases p969_3 (m.d 3 5) (by simp) with h991 | h991
                                  · linarith only [h962, h991, hlam]
                                  · linarith only [h967, h991, hlam]
                              · linarith only [h965, h988, hlam]
                            · linarith only [h987, hlam, p969_0]
                          · linarith only [h772, h986, hlam]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p969_1, u5ehi3]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht12, p969_1, u1ehi2]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [hc23, hlam, hphi, ht12, p969_1, u1ehi2]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          rcases p969_3 (m.d 0 3) (by simp) with h1001 | h1001
                          · linarith only [h1001, h4, hlam]
                          · linarith only [h1001, h772, hlam]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          rcases p969_3 (m.d 0 3) (by simp) with h1004 | h1004
                          · linarith only [h1004, h4, hlam]
                          · linarith only [h1004, h773, hlam]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h772, hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h961, hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h965, hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h967, hlam, p969_1]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h773, hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h962, hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h966, hlam, p969_0]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [h1, h962, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p969_1]
                        · have p969_0 := h969c.1
                          have p969_1 := h969c.2.1
                          have p969_2 := h969c.2.2.1
                          have p969_3 := h969c.2.2.2
                          linarith only [hlam, p969_0]
                    · linarith only [h0, h4, h966, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h0, h4, h965, hc34, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h4, h773, h962, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h4, h772, h898, h961, hc23, hlam, hphi, ht12, u1ehi1]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1021 | h1021
      · linarith only [h1021, h772, h773, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1023 | h1023
        · linarith only [h0, h1023, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1025 | h1025
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1026 | h1026
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1027 | h1027
              · linarith only [h1, h1027, h773, hlam]
              · linarith only [h1023, h1025, h1027, hlam]
            · linarith only [h1023, h1025, h1026, h772, h773, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1031 | h1031
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1032 | h1032
              · linarith only [h1, h1032, h773, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1034 | h1034
                · linarith only [h1021, h1034, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1036 | h1036
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1037 | h1037
                    · linarith only [h1037, h2, h772, h773, hc23, hlam, hphi, ht12, u1ehi3]
                    · linarith only [h0, h1037, h4, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h0, h1031, h1036, h4, hc13, hlam, hphi, u1ehi1]
            · linarith only [h1031, h4, h772, hc23, hlam, hphi, ht12, u1ehi2]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1042 | h1042
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1043 | h1043
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1044 | h1044
        · linarith only [h0, h1044, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1046 | h1046
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1047 | h1047
            · linarith only [h1, h1047, h772, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1049 | h1049
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1050 | h1050
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1051 | h1051
                  · linarith only [h1, h1044, h1046, h1051, h772, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h0, h1046, h1051, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · linarith only [h1043, h1044, h1046, h1047, h1050, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
              · linarith only [h1042, h1044, h1046, h1049, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1056 | h1056
            · linarith only [h1, h1042, h1056, h772, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1058 | h1058
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1059 | h1059
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1060 | h1060
                  · linarith only [h1, h1060, h772, hc23, hlam, hphi, ht12, u1ehi2]
                  · linarith only [h0, h1060, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h1043, h1056, h1058, h1059, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h1042, h1058, h4, hc23, hlam, hphi, ht12, u1ehi2]
      · linarith only [h1042, h1043, h772, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1066 | h1066
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1067 | h1067
        · linarith only [h0, h1067, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1069 | h1069
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1070 | h1070
            · linarith only [h1, h1070, h772, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1072 | h1072
              · linarith only [h0, h1042, h1069, h1072, h4, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h1067, h1069, h1072, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1075 | h1075
            · linarith only [h1, h1066, h1075, h772, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1077 | h1077
              · linarith only [h1, h1042, h1077, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1079 | h1079
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1080 | h1080
                  · linarith only [h0, h1080, h4, h772, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h0, h1080, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h1066, h1079, h772, hc34, hlam, hphi, ht12, ht23, u1ehi3]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1084 | h1084
        · linarith only [h0, h1084, h4, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1086 | h1086
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1087 | h1087
            · linarith only [h1, h1087, h772, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1089 | h1089
              · linarith only [h1, h1042, h1089, hlam]
              · linarith only [h1084, h1086, h1089, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1092 | h1092
            · linarith only [h0, h1092, h4, h772, hc13, hlam, hphi, u1ehi1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1094 | h1094
              · linarith only [h1, h1042, h1094, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1096 | h1096
                · linarith only [h1066, h1096, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1098 | h1098
                  · linarith only [h0, h1098, h4, h772, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h0, h1098, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 3038000 in
set_option maxHeartbeats 3038000 in
theorem r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 3038000 in
set_option maxHeartbeats 3038000 in
theorem r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]

set_option maxHeartbeats 3038000 in
set_option maxHeartbeats 3038000 in
theorem r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 3038000 in
set_option maxHeartbeats 3038000 in
theorem r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]

set_option maxHeartbeats 3038000 in
set_option maxHeartbeats 3038000 in
theorem r1l7_11_13_25_L_R_L_I_M_IR_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2
  · exact r1l7_11_13_25_L_R_L_I_M_IR_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2

set_option maxHeartbeats 3038000 in
set_option maxHeartbeats 3038000 in
theorem r1l7_11_13_25_L_R_L_I_M_IR_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]

set_option maxHeartbeats 3038000 in
set_option maxHeartbeats 3038000 in
theorem r1l7_11_13_25_L_R_L_I_M_IR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_13_25_L_R_L_I_M_IR_x0_x0 m hb1 hb3 hb5 h0 h1
  · exact r1l7_11_13_25_L_R_L_I_M_IR_x0_x1 m hb1 hb3 hb5 h0 h1

set_option maxHeartbeats 3038000 in
set_option maxHeartbeats 3038000 in
theorem r1l7_11_13_25_L_R_L_I_M_IR_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1104 | h1104
  · linarith only [h0, h1104, hc12, hlam, hphi, u1ehi2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1106 | h1106
    · linarith only [h0, h1106, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1108 | h1108
      · linarith only [h0, h1108, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1110 | h1110
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1111 | h1111
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1112 | h1112
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1113 | h1113
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1114 | h1114
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1115 | h1115
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1116 | h1116
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1117 | h1117
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1118 | h1118
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1119 | h1119
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1120 | h1120
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1121 | h1121
                              · linarith only [h1110, h1119, h1121, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases h3bigk with h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1104, hlam, p1123_1]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1104, h1114, h1120, hc12, hlam, hphi, ht01, ht0b, ht5b, p1123_1, u5ehi3]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  rcases p1123_3 (m.d 0 3) (by simp) with h1127 | h1127
                                  · rcases p1123_3 (m.d 1 3) (by simp) with h1128 | h1128
                                    · rcases p1123_3 (m.d 2 3) (by simp) with h1129 | h1129
                                      · linarith only [h1110, h1129, hlam]
                                      · linarith only [h1119, h1129, hlam]
                                    · linarith only [h1116, h1128, hlam]
                                  · linarith only [h1127, hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  rcases p1123_3 (m.d 0 3) (by simp) with h1134 | h1134
                                  · rcases p1123_3 (m.d 1 3) (by simp) with h1135 | h1135
                                    · rcases p1123_3 (m.d 2 3) (by simp) with h1136 | h1136
                                      · linarith only [h1110, h1136, hlam]
                                      · linarith only [h1120, h1136, hlam]
                                    · linarith only [h1117, h1135, hlam]
                                  · linarith only [h1134, hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1104, h1114, hc12, hlam, hphi, p1123_1, u1ehi0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1114, h1120, hc12, hlam, hphi, ht01, ht0b, ht5b, p1123_1, u5ehi3]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  rcases p1123_3 (m.d 0 3) (by simp) with h1144 | h1144
                                  · linarith only [h1104, h1144, hlam]
                                  · linarith only [h1111, h1144, hlam]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  rcases p1123_3 (m.d 0 3) (by simp) with h1147 | h1147
                                  · linarith only [h1104, h1147, hlam]
                                  · linarith only [h1112, h1147, hlam]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1110, hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1114, hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  rcases p1123_3 (m.d 0 3) (by simp) with h1153 | h1153
                                  · rcases p1123_3 (m.d 1 3) (by simp) with h1154 | h1154
                                    · rcases p1123_3 (m.d 2 3) (by simp) with h1155 | h1155
                                      · rcases p1123_3 (m.d 3 4) (by simp) with h1156 | h1156
                                        · linarith only [h1156, hlam, p1123_0]
                                        · rcases p1123_3 (m.d 3 5) (by simp) with h1158 | h1158
                                          · linarith only [h1120, h1158, hlam]
                                          · linarith only [h1121, h1158, hlam]
                                      · linarith only [h1155, hlam, p1123_0]
                                    · linarith only [h1116, h1154, hlam]
                                  · linarith only [h1111, h1153, hlam]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h0, h1110, hc12, hlam, hphi, ht01, ht0b, ht5b, p1123_1, u5ehi3]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1111, hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1116, hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1119, hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1121, hlam, p1123_1]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1112, hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1117, hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h1120, hlam, p1123_0]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [h0, h1110, h1120, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1123_1]
                                · have p1123_0 := h1123c.1
                                  have p1123_1 := h1123c.2.1
                                  have p1123_2 := h1123c.2.2.1
                                  have p1123_3 := h1123c.2.2.2
                                  linarith only [hlam, p1123_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1175 | h1175
                              · linarith only [h1112, h1113, h1119, h1120, h1175, hc04, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases h3bigk with h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c | h1177c
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1104, hlam, p1177_1]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  rcases p1177_3 (m.d 0 3) (by simp) with h1180 | h1180
                                  · rcases p1177_3 (m.d 1 3) (by simp) with h1181 | h1181
                                    · rcases p1177_3 (m.d 2 3) (by simp) with h1182 | h1182
                                      · linarith only [h1110, h1182, hlam]
                                      · rcases p1177_3 (m.d 3 4) (by simp) with h1184 | h1184
                                        · linarith only [h1111, h1184, hlam]
                                        · rcases p1177_3 (m.d 3 5) (by simp) with h1186 | h1186
                                          · linarith only [h1112, h1186, hlam]
                                          · linarith only [h1120, h1186, hlam]
                                    · linarith only [h1114, h1181, hlam]
                                  · linarith only [h1110, h1180, hlam]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1111, h1113, h1119, h1120, h1175, hlam, p1177_2]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1119, h1120, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1177_1]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1104, h1114, hc12, hlam, hphi, p1177_1, u1ehi0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  rcases p1177_3 (m.d 0 3) (by simp) with h1195 | h1195
                                  · linarith only [h1104, h1195, hlam]
                                  · linarith only [h1110, h1195, hlam]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1106, h1113, h1116, h1119, h1120, h1175, hlam, p1177_2]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1114, h1119, h1120, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1177_1]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1110, hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1114, hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1111, h1113, h1120, h1175, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1177_1]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1120, hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1111, hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1116, hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1119, hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1175, hlam, p1177_1]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1112, hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1117, hlam, p1177_0]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [h1104, h1111, h1113, h1114, h1119, h1175, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1177_1]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  rcases p1177_3 (m.d 0 3) (by simp) with h1213 | h1213
                                  · rcases p1177_3 (m.d 1 3) (by simp) with h1214 | h1214
                                    · rcases p1177_3 (m.d 2 3) (by simp) with h1215 | h1215
                                      · linarith only [h1120, h1215, hlam]
                                      · linarith only [h1119, h1215, hlam]
                                    · linarith only [h1116, h1214, hlam]
                                  · linarith only [h1111, h1213, hlam]
                                · have p1177_0 := h1177c.1
                                  have p1177_1 := h1177c.2.1
                                  have p1177_2 := h1177c.2.2.1
                                  have p1177_3 := h1177c.2.2.2
                                  linarith only [hlam, p1177_0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1221 | h1221
                            · linarith only [h1104, h1111, h1114, h1119, h1221, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1223 | h1223
                              · rcases h3bigk with h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1104, hlam, p1224_1]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  rcases p1224_3 (m.d 0 3) (by simp) with h1227 | h1227
                                  · rcases p1224_3 (m.d 1 3) (by simp) with h1228 | h1228
                                    · rcases p1224_3 (m.d 2 3) (by simp) with h1229 | h1229
                                      · linarith only [h1110, h1229, hlam]
                                      · rcases p1224_3 (m.d 3 4) (by simp) with h1231 | h1231
                                        · linarith only [h1111, h1231, hlam]
                                        · linarith only [h1119, h1231, hlam]
                                    · linarith only [h1114, h1228, hlam]
                                  · linarith only [h1110, h1227, hlam]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1104, h1114, h1223, hc12, hlam, hphi, ht01, ht0b, ht5b, p1224_1, u5ehi4]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  rcases p1224_3 (m.d 0 3) (by simp) with h1237 | h1237
                                  · rcases p1224_3 (m.d 1 3) (by simp) with h1238 | h1238
                                    · rcases p1224_3 (m.d 2 3) (by simp) with h1239 | h1239
                                      · linarith only [h1110, h1239, hlam]
                                      · rcases p1224_3 (m.d 3 4) (by simp) with h1241 | h1241
                                        · linarith only [h1111, h1241, hlam]
                                        · linarith only [h1223, h1241, hlam]
                                    · linarith only [h1117, h1238, hlam]
                                  · linarith only [h1237, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1104, h1114, hc12, hlam, hphi, p1224_1, u1ehi0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  rcases p1224_3 (m.d 0 3) (by simp) with h1248 | h1248
                                  · linarith only [h1104, h1248, hlam]
                                  · linarith only [h1110, h1248, hlam]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1114, h1223, hc12, hlam, hphi, ht01, ht0b, ht5b, p1224_1, u5ehi4]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  rcases p1224_3 (m.d 0 3) (by simp) with h1252 | h1252
                                  · linarith only [h1104, h1252, hlam]
                                  · linarith only [h1112, h1252, hlam]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1110, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1114, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1119, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1221, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1111, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1116, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  rcases p1224_3 (m.d 0 3) (by simp) with h1262 | h1262
                                  · rcases p1224_3 (m.d 1 3) (by simp) with h1263 | h1263
                                    · rcases p1224_3 (m.d 2 3) (by simp) with h1264 | h1264
                                      · linarith only [h1264, hlam, p1224_0]
                                      · rcases p1224_3 (m.d 3 4) (by simp) with h1266 | h1266
                                        · rcases p1224_3 (m.d 3 5) (by simp) with h1267 | h1267
                                          · linarith only [h1223, h1267, hlam]
                                          · linarith only [h1221, h1267, hlam]
                                        · linarith only [h1266, hlam, p1224_0]
                                    · linarith only [h1114, h1263, hlam]
                                  · linarith only [h1110, h1262, hlam]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1111, h1221, hc03, hlam, hphi, ht0b, ht5b, p1224_1, u5ehi2]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1112, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1117, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  rcases p1224_3 (m.d 0 3) (by simp) with h1277 | h1277
                                  · rcases p1224_3 (m.d 1 3) (by simp) with h1278 | h1278
                                    · rcases p1224_3 (m.d 2 3) (by simp) with h1279 | h1279
                                      · linarith only [h1279, hlam, p1224_0]
                                      · rcases p1224_3 (m.d 3 4) (by simp) with h1281 | h1281
                                        · rcases p1224_3 (m.d 3 5) (by simp) with h1282 | h1282
                                          · rcases h5bigk with h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c | h1283c
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [hlam, p1283_0]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1108, hlam, p1283_1]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              rcases p1283_3 (m.d 0 5) (by simp) with h1286 | h1286
                                              · rcases p1283_3 (m.d 1 5) (by simp) with h1287 | h1287
                                                · rcases p1283_3 (m.d 2 5) (by simp) with h1288 | h1288
                                                  · linarith only [h1288, hlam, p1283_0]
                                                  · rcases p1283_3 (m.d 3 5) (by simp) with h1290 | h1290
                                                    · linarith only [h1112, h1290, hlam]
                                                    · linarith only [h1221, h1290, hlam]
                                                · linarith only [h1115, h1287, hlam]
                                              · linarith only [h1286, hlam, p1283_0]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1113, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1224_1, p1283_1]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              rcases p1283_3 (m.d 0 5) (by simp) with h1296 | h1296
                                              · rcases p1283_3 (m.d 1 5) (by simp) with h1297 | h1297
                                                · rcases p1283_3 (m.d 2 5) (by simp) with h1298 | h1298
                                                  · linarith only [h1115, h1298, hc12, hlam, hphi, ht01, ht0b, ht5b, p1283_1, u5ehi4]
                                                  · rcases p1283_3 (m.d 3 5) (by simp) with h1300 | h1300
                                                    · linarith only [h1112, h1300, hlam]
                                                    · linarith only [h1223, h1300, hlam]
                                                · linarith only [h1118, h1297, hlam]
                                              · linarith only [h1113, h1296, hlam]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1108, h1114, h1116, h1118, hc12, hlam, hphi, p1283_1, u1ehi0]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [hlam, p1283_0]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              rcases p1283_3 (m.d 0 5) (by simp) with h1307 | h1307
                                              · linarith only [h1108, h1307, hlam]
                                              · linarith only [h1112, h1114, h1116, h1118, h1307, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1224_1, p1283_1]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1114, h1116, h1118, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1224_1, p1283_1]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              rcases p1283_3 (m.d 0 5) (by simp) with h1311 | h1311
                                              · linarith only [h1108, h1311, hlam]
                                              · linarith only [h1113, h1311, hlam]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1112, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1224_1, p1283_1]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1115, hlam, p1283_1]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [hlam, p1283_0]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1221, hlam, p1283_1]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1104, h1112, h1114, h1221, hc12, hlam, hphi, ht01, ht0b, ht5b, p1283_1, u5ehi4]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1112, hlam, p1283_0]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1117, hlam, p1283_0]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1104, h1112, h1114, hc12, hlam, hphi, ht01, ht0b, ht5b, p1283_1, u5ehi2]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [hlam, p1283_0]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1104, h1111, h1114, h1223, hc12, hlam, hphi, ht01, ht0b, ht5b, p1283_1, u5ehi4]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1113, hlam, p1283_0]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1118, hlam, p1283_0]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1106, h1113, h1114, h1116, hc12, hlam, hphi, ht01, ht0b, ht5b, p1283_1, u5ehi2]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [h1223, hlam, p1283_0]
                                            · have p1283_0 := h1283c.1
                                              have p1283_1 := h1283c.2.1
                                              have p1283_2 := h1283c.2.2.1
                                              have p1283_3 := h1283c.2.2.2
                                              linarith only [hlam, p1283_0]
                                          · linarith only [h1282, hlam, p1224_0]
                                        · linarith only [h1119, h1281, hlam]
                                    · linarith only [h1114, h1278, hlam]
                                  · linarith only [h1110, h1277, hlam]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [h1223, hlam, p1224_0]
                                · have p1224_0 := h1224c.1
                                  have p1224_1 := h1224c.2.1
                                  have p1224_2 := h1224c.2.2.1
                                  have p1224_3 := h1224c.2.2.2
                                  linarith only [hlam, p1224_0]
                              · rcases h3bigk with h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c | h1335c
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1104, hlam, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1111, h1113, h1119, h1223, hlam, p1335_2]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  rcases p1335_3 (m.d 0 3) (by simp) with h1339 | h1339
                                  · rcases p1335_3 (m.d 1 3) (by simp) with h1340 | h1340
                                    · rcases p1335_3 (m.d 2 3) (by simp) with h1341 | h1341
                                      · linarith only [h1110, h1341, hlam]
                                      · rcases p1335_3 (m.d 3 4) (by simp) with h1343 | h1343
                                        · linarith only [h1343, hlam, p1335_0]
                                        · rcases p1335_3 (m.d 3 5) (by simp) with h1345 | h1345
                                          · linarith only [h1112, h1345, hlam]
                                          · linarith only [h1223, h1345, hlam]
                                    · linarith only [h1116, h1340, hlam]
                                  · linarith only [h1339, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  rcases p1335_3 (m.d 0 3) (by simp) with h1350 | h1350
                                  · rcases p1335_3 (m.d 1 3) (by simp) with h1351 | h1351
                                    · rcases p1335_3 (m.d 2 3) (by simp) with h1352 | h1352
                                      · linarith only [h1110, h1352, hlam]
                                      · rcases p1335_3 (m.d 3 4) (by simp) with h1354 | h1354
                                        · linarith only [h1111, h1354, hlam]
                                        · rcases p1335_3 (m.d 3 5) (by simp) with h1356 | h1356
                                          · linarith only [h1356, hlam, p1335_0]
                                          · rcases h5bigk with h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [hlam, p1358_0]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1108, hlam, p1358_1]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              rcases p1358_3 (m.d 0 5) (by simp) with h1361 | h1361
                                              · rcases p1358_3 (m.d 1 5) (by simp) with h1362 | h1362
                                                · rcases p1358_3 (m.d 2 5) (by simp) with h1363 | h1363
                                                  · linarith only [h1363, hlam, p1358_0]
                                                  · rcases p1358_3 (m.d 3 5) (by simp) with h1365 | h1365
                                                    · linarith only [h1112, h1365, hlam]
                                                    · linarith only [h1221, h1365, hlam]
                                                · linarith only [h1115, h1362, hlam]
                                              · linarith only [h1361, hlam, p1358_0]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              rcases p1358_3 (m.d 0 5) (by simp) with h1370 | h1370
                                              · rcases p1358_3 (m.d 1 5) (by simp) with h1371 | h1371
                                                · rcases p1358_3 (m.d 2 5) (by simp) with h1372 | h1372
                                                  · linarith only [h1115, h1119, h1223, h1372, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1358_1]
                                                  · rcases p1358_3 (m.d 3 5) (by simp) with h1374 | h1374
                                                    · linarith only [h1112, h1374, hlam]
                                                    · rcases p1358_3 (m.d 4 5) (by simp) with h1376 | h1376
                                                      · linarith only [h1113, h1376, hlam]
                                                      · linarith only [h1223, h1376, hlam]
                                                · linarith only [h1117, h1371, hlam]
                                              · linarith only [h1112, h1370, hlam]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1108, h1114, h1116, h1118, h1119, h1223, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1358_1]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1108, h1114, h1116, h1118, hc12, hlam, hphi, p1358_1, u1ehi0]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [hlam, p1358_0]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              rcases p1358_3 (m.d 0 5) (by simp) with h1384 | h1384
                                              · linarith only [h1108, h1384, hlam]
                                              · linarith only [h1113, h1119, h1221, h1223, h1384, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1335_1]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              rcases p1358_3 (m.d 0 5) (by simp) with h1387 | h1387
                                              · linarith only [h1108, h1387, hlam]
                                              · linarith only [h1112, h1387, hlam]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1114, h1116, h1118, h1119, h1223, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1358_1]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1113, h1119, h1223, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1358_1]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1115, hlam, p1358_1]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [hlam, p1358_0]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1221, hlam, p1358_1]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1104, h1114, h1119, h1221, h1223, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1335_1, p1358_1]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1112, hlam, p1358_0]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1117, hlam, p1358_0]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1104, h1114, hc12, hlam, hphi, ht01, ht0b, ht5b, p1335_1, p1358_1, u5ehi2]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [hlam, p1358_0]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1223, hlam, p1358_1]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1113, hlam, p1358_0]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1118, hlam, p1358_0]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1106, h1113, h1114, h1116, hc12, hlam, hphi, ht01, ht0b, ht5b, p1358_1, u5ehi2]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [h1106, h1113, h1114, h1116, hc12, hlam, hphi, ht01, ht0b, ht5b, p1358_1, u5ehi3]
                                            · have p1358_0 := h1358c.1
                                              have p1358_1 := h1358c.2.1
                                              have p1358_2 := h1358c.2.2.1
                                              have p1358_3 := h1358c.2.2.2
                                              linarith only [hlam, p1358_0]
                                    · linarith only [h1117, h1351, hlam]
                                  · linarith only [h1350, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1104, h1114, hc12, hlam, hphi, p1335_1, u1ehi0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1106, h1113, h1116, h1119, h1223, hlam, p1335_2]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  rcases p1335_3 (m.d 0 3) (by simp) with h1411 | h1411
                                  · linarith only [h1104, h1411, hlam]
                                  · linarith only [h1111, h1411, hlam]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  rcases p1335_3 (m.d 0 3) (by simp) with h1414 | h1414
                                  · linarith only [h1104, h1414, hlam]
                                  · linarith only [h1112, h1414, hlam]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1110, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1114, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1119, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1221, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1111, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1116, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1106, h1113, h1114, h1116, h1223, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1223, hlam, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1112, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1117, hlam, p1335_0]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  rcases p1335_3 (m.d 0 3) (by simp) with h1429 | h1429
                                  · rcases p1335_3 (m.d 1 3) (by simp) with h1430 | h1430
                                    · rcases p1335_3 (m.d 2 3) (by simp) with h1431 | h1431
                                      · linarith only [h1431, hlam, p1335_0]
                                      · rcases p1335_3 (m.d 3 4) (by simp) with h1433 | h1433
                                        · linarith only [h1223, h1433, hlam]
                                        · linarith only [h1119, h1433, hlam]
                                    · linarith only [h1114, h1430, hlam]
                                  · linarith only [h1110, h1429, hlam]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [h1104, h1112, h1114, h1119, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1335_1]
                                · have p1335_0 := h1335c.1
                                  have p1335_1 := h1335c.2.1
                                  have p1335_2 := h1335c.2.2.1
                                  have p1335_3 := h1335c.2.2.2
                                  linarith only [hlam, p1335_0]
                        · linarith only [h1106, h1118, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                      · linarith only [h1104, h1112, h1117, hlam]
                    · linarith only [h1104, h1116, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h1115, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h1114, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1445 | h1445
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1446 | h1446
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1447 | h1447
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1448 | h1448
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1449 | h1449
                        · linarith only [h1106, h1113, h1445, h1447, h1449, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h1106, h1449, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                      · linarith only [h0, h1110, h1112, h1448, hc12, hlam, hphi, u1ehi2]
                    · linarith only [h1104, h1447, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h1446, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h1110, h1445, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1456 | h1456
              · linarith only [h1111, h1112, h1456, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1458 | h1458
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1459 | h1459
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1460 | h1460
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1461 | h1461
                      · linarith only [h1104, h1112, h1458, h1461, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h1104, h1461, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h1104, h1110, h1111, h1460, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                  · linarith only [h0, h1459, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h1110, h1458, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1467 | h1467
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1468 | h1468
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1469 | h1469
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1470 | h1470
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1471 | h1471
                    · linarith only [h1111, h1467, h1469, h1471, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h1104, h1471, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h1470, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h1110, h1469, hlam]
              · linarith only [h1111, h1467, h1468, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1477 | h1477
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1478 | h1478
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1479 | h1479
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1480 | h1480
                    · linarith only [h1104, h1111, h1478, h1480, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h1104, h1480, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h1479, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h1110, h1478, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1485 | h1485
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1486 | h1486
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1487 | h1487
                    · linarith only [h1104, h1111, h1485, h1487, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h1104, h1487, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                  · linarith only [h0, h1486, hc25, hlam, hphi, ht12, u1ehi0]
                · linarith only [h0, h1110, h1485, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1492 | h1492
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1493 | h1493
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1494 | h1494
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1495 | h1495
                · linarith only [h0, h1110, h1495, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h1495, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1498 | h1498
                · linarith only [h0, h1110, h1498, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h1498, hc23, hlam, hphi, ht12, u1ehi0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1501 | h1501
              · linarith only [h1492, h1493, h1501, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1503 | h1503
                · linarith only [h0, h1110, h1503, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h1503, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1506 | h1506
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1507 | h1507
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1508 | h1508
                · linarith only [h0, h1110, h1508, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h1508, hc23, hlam, hphi, ht12, u1ehi0]
              · linarith only [h1492, h1506, h1507, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1512 | h1512
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1513 | h1513
                · linarith only [h0, h1110, h1513, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h1513, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1516 | h1516
                · linarith only [h0, h1110, h1516, hc12, hlam, hphi, u1ehi0]
                · linarith only [h0, h1516, hc23, hlam, hphi, ht12, u1ehi0]

set_option maxHeartbeats 3038000 in
set_option maxHeartbeats 3038000 in
theorem r1l7_11_13_25_L_R_L_I_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_R_L_I_M_IR_x0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_R_L_I_M_IR_x1 m hb1 hb3 hb5 h0

end R2N4
