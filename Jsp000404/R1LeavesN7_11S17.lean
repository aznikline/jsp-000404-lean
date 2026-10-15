import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10016 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10017 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h10018 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h10019 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 2 3 4 (by decide) (by decide) with h10809 | h10809
  · rcases m.htr 2 3 5 (by decide) (by decide) with h10810 | h10810
    · rcases m.htr 2 4 5 (by decide) (by decide) with h10811 | h10811
      · linarith only [h10016, h10019, h10811, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h10813 | h10813
        · linarith only [h10017, h10019, h10813, hlam]
        · rcases h2bigk with h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c | h10815c
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [h0, hlam, p10815_1]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            rcases p10815_3 (m.d 0 2) (by simp) with h10818 | h10818
            · rcases p10815_3 (m.d 1 2) (by simp) with h10819 | h10819
              · rcases p10815_3 (m.d 2 3) (by simp) with h10820 | h10820
                · linarith only [h10820, hlam, p10815_0]
                · rcases p10815_3 (m.d 2 4) (by simp) with h10822 | h10822
                  · linarith only [h10010, h10822, hlam]
                  · rcases p10815_3 (m.d 2 5) (by simp) with h10824 | h10824
                    · linarith only [h10011, h10824, hlam]
                    · rcases h3bigk with h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c | h10826c
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h8410, hlam, p10826_1]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        rcases p10826_3 (m.d 0 3) (by simp) with h10829 | h10829
                        · rcases p10826_3 (m.d 1 3) (by simp) with h10830 | h10830
                          · rcases p10826_3 (m.d 2 3) (by simp) with h10831 | h10831
                            · linarith only [h10009, h10831, hlam]
                            · rcases p10826_3 (m.d 3 4) (by simp) with h10833 | h10833
                              · linarith only [h10012, h10833, hlam]
                              · rcases p10826_3 (m.d 3 5) (by simp) with h10835 | h10835
                                · linarith only [h10013, h10835, hlam]
                                · rcases h5bigk with h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c | h10837c
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [hlam, p10837_0]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10008, h10015, h8410, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10008, h10015, h10810, h8410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10008, h10015, h8410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10008, h10015, h10017, h10019, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10008, hlam, p10837_0]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [hlam, p10837_0]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10008, h10015, h10810, h8410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10008, h10015, h8410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10019, hlam, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10011, hlam, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10016, hlam, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [hlam, p10837_0]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h0, h10011, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10811, hlam, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10013, hlam, p10837_0]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10018, hlam, p10837_0]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10810, hlam, p10837_0]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [hlam, p10837_0]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10813, hlam, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h10014, hlam, p10837_0]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h0, h10009, h10012, h10014, h10016, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h0, h10009, h10012, h10014, h10810, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [h0, h10009, h10012, h10014, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10837_1]
                                  · have p10837_0 := h10837c.1
                                    have p10837_1 := h10837c.2.1
                                    have p10837_2 := h10837c.2.2.1
                                    have p10837_3 := h10837c.2.2.2
                                    linarith only [hlam, p10837_0]
                          · linarith only [h10015, h10830, hlam]
                        · linarith only [h10009, h10829, hlam]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        rcases p10826_3 (m.d 0 3) (by simp) with h10865 | h10865
                        · rcases p10826_3 (m.d 1 3) (by simp) with h10866 | h10866
                          · rcases p10826_3 (m.d 2 3) (by simp) with h10867 | h10867
                            · linarith only [h10009, h10867, hlam]
                            · linarith only [h10809, h10867, hlam]
                          · linarith only [h10017, h10866, hlam]
                        · linarith only [h10865, hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        rcases p10826_3 (m.d 0 3) (by simp) with h10872 | h10872
                        · rcases p10826_3 (m.d 1 3) (by simp) with h10873 | h10873
                          · rcases p10826_3 (m.d 2 3) (by simp) with h10874 | h10874
                            · linarith only [h10009, h10874, hlam]
                            · linarith only [h10810, h10874, hlam]
                          · linarith only [h10018, h10873, hlam]
                        · linarith only [h10872, hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h10015, hc12, hlam, hphi, ht01, p10826_1, u0ehi2]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        rcases p10826_3 (m.d 0 3) (by simp) with h10881 | h10881
                        · linarith only [h10881, h8410, hlam]
                        · linarith only [h10009, h10881, hlam]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        rcases p10826_3 (m.d 0 3) (by simp) with h10884 | h10884
                        · linarith only [h10884, h8410, hlam]
                        · linarith only [h10012, h10884, hlam]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        rcases p10826_3 (m.d 0 3) (by simp) with h10887 | h10887
                        · linarith only [h10887, h8410, hlam]
                        · linarith only [h10013, h10887, hlam]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h10009, hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h10015, hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10815_1, p10826_1]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h0, h10813, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10815_1, p10826_1]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h10012, hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h10017, hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h10809, hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h10813, hlam, p10826_1]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h10013, hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h10018, hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h10810, hlam, p10826_0]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [h10008, h10018, h8410, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10826_1]
                      · have p10826_0 := h10826c.1
                        have p10826_1 := h10826c.2.1
                        have p10826_2 := h10826c.2.2.1
                        have p10826_3 := h10826c.2.2.2
                        linarith only [hlam, p10826_0]
              · linarith only [h10015, h10819, hlam]
            · linarith only [h10818, hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            rcases p10815_3 (m.d 0 2) (by simp) with h10907 | h10907
            · rcases p10815_3 (m.d 1 2) (by simp) with h10908 | h10908
              · rcases p10815_3 (m.d 2 3) (by simp) with h10909 | h10909
                · linarith only [h10009, h10909, hlam]
                · linarith only [h10809, h10909, hlam]
              · linarith only [h0, h10908, hlam, p10815_1]
            · linarith only [h10907, hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            rcases p10815_3 (m.d 0 2) (by simp) with h10914 | h10914
            · rcases p10815_3 (m.d 1 2) (by simp) with h10915 | h10915
              · rcases p10815_3 (m.d 2 3) (by simp) with h10916 | h10916
                · linarith only [h10009, h10916, hlam]
                · linarith only [h10810, h10916, hlam]
              · linarith only [h10016, h10915, hlam]
            · linarith only [h10914, hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [hc12, hlam, hphi, ht01, p10815_1, u0ehi1]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            rcases p10815_3 (m.d 0 2) (by simp) with h10923 | h10923
            · linarith only [h0, h10923, hlam]
            · linarith only [h10009, h10923, hlam]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            rcases p10815_3 (m.d 0 2) (by simp) with h10926 | h10926
            · linarith only [h0, h10926, hlam]
            · linarith only [h10010, h10926, hlam]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            rcases p10815_3 (m.d 0 2) (by simp) with h10929 | h10929
            · linarith only [h0, h10929, hlam]
            · linarith only [h10011, h10929, hlam]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [h10009, hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [h10015, hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            rcases p10815_3 (m.d 0 2) (by simp) with h10935 | h10935
            · rcases p10815_3 (m.d 1 2) (by simp) with h10936 | h10936
              · rcases p10815_3 (m.d 2 3) (by simp) with h10937 | h10937
                · rcases p10815_3 (m.d 2 4) (by simp) with h10938 | h10938
                  · linarith only [h10809, h10938, hlam]
                  · rcases p10815_3 (m.d 2 5) (by simp) with h10940 | h10940
                    · linarith only [h10810, h10940, hlam]
                    · linarith only [h10811, h10940, hlam]
                · linarith only [h10809, h10937, hlam]
              · linarith only [h10009, h10015, h10936, h8410, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10815_1]
            · linarith only [h10010, h10935, hlam]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            rcases p10815_3 (m.d 0 2) (by simp) with h10946 | h10946
            · rcases p10815_3 (m.d 1 2) (by simp) with h10947 | h10947
              · rcases p10815_3 (m.d 2 3) (by simp) with h10948 | h10948
                · rcases p10815_3 (m.d 2 4) (by simp) with h10949 | h10949
                  · linarith only [h10809, h10949, hlam]
                  · rcases p10815_3 (m.d 2 5) (by simp) with h10951 | h10951
                    · linarith only [h10810, h10951, hlam]
                    · rcases h3bigk with h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c | h10953c
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h8410, hlam, p10953_1]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10809, h10811, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10815_1, p10953_1]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        rcases p10953_3 (m.d 0 3) (by simp) with h10957 | h10957
                        · rcases p10953_3 (m.d 1 3) (by simp) with h10958 | h10958
                          · rcases p10953_3 (m.d 2 3) (by simp) with h10959 | h10959
                            · linarith only [h10009, h10959, hlam]
                            · linarith only [h10809, h10959, hlam]
                          · linarith only [h10017, h10958, hlam]
                        · linarith only [h10957, hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        rcases p10953_3 (m.d 0 3) (by simp) with h10964 | h10964
                        · rcases p10953_3 (m.d 1 3) (by simp) with h10965 | h10965
                          · rcases p10953_3 (m.d 2 3) (by simp) with h10966 | h10966
                            · linarith only [h10009, h10966, hlam]
                            · linarith only [h10810, h10966, hlam]
                          · linarith only [h10018, h10965, hlam]
                        · linarith only [h10964, hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10015, hc12, hlam, hphi, ht01, p10953_1, u0ehi2]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10015, h10809, h10811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10815_1, p10953_1]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        rcases p10953_3 (m.d 0 3) (by simp) with h10974 | h10974
                        · linarith only [h10974, h8410, hlam]
                        · linarith only [h10012, h10974, hlam]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        rcases p10953_3 (m.d 0 3) (by simp) with h10977 | h10977
                        · linarith only [h10977, h8410, hlam]
                        · linarith only [h10013, h10977, hlam]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10009, hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10015, hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        rcases p10953_3 (m.d 0 3) (by simp) with h10983 | h10983
                        · rcases p10953_3 (m.d 1 3) (by simp) with h10984 | h10984
                          · rcases p10953_3 (m.d 2 3) (by simp) with h10985 | h10985
                            · rcases p10953_3 (m.d 3 4) (by simp) with h10986 | h10986
                              · linarith only [h10986, hlam, p10953_0]
                              · rcases p10953_3 (m.d 3 5) (by simp) with h10988 | h10988
                                · linarith only [h10810, h10988, hlam]
                                · linarith only [h10813, h10988, hlam]
                            · linarith only [h10985, hlam, p10953_0]
                          · linarith only [h10017, h10984, hlam]
                        · linarith only [h10012, h10983, hlam]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        rcases p10953_3 (m.d 0 3) (by simp) with h10994 | h10994
                        · rcases p10953_3 (m.d 1 3) (by simp) with h10995 | h10995
                          · rcases p10953_3 (m.d 2 3) (by simp) with h10996 | h10996
                            · rcases p10953_3 (m.d 3 4) (by simp) with h10997 | h10997
                              · linarith only [h10809, h10997, hlam]
                              · rcases p10953_3 (m.d 3 5) (by simp) with h10999 | h10999
                                · linarith only [h10999, hlam, p10953_0]
                                · rcases h5bigk with h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c | h11001c
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [hlam, p11001_0]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h0, h10008, h10016, h10809, h10811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h0, h10008, h10809, h10811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h0, h10008, h10813, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h0, h10008, h10017, h10019, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10008, hlam, p11001_0]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [hlam, p11001_0]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h0, h10008, h10809, h10811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10008, h10015, h10813, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10019, hlam, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10011, hlam, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10016, hlam, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [hlam, p11001_0]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10009, h10813, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p10815_1, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10811, hlam, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10013, hlam, p11001_0]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10018, hlam, p11001_0]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10810, hlam, p11001_0]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [hlam, p11001_0]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10813, hlam, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10014, hlam, p11001_0]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10012, h10014, hc03, hc15, hlam, hphi, ht0b, ht5b, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10012, h10014, h10015, h10810, h10813, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [h10012, h10014, h10015, h10813, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11001_1]
                                  · have p11001_0 := h11001c.1
                                    have p11001_1 := h11001c.2.1
                                    have p11001_2 := h11001c.2.2.1
                                    have p11001_3 := h11001c.2.2.2
                                    linarith only [hlam, p11001_0]
                            · linarith only [h10996, hlam, p10953_0]
                          · linarith only [h10018, h10995, hlam]
                        · linarith only [h10013, h10994, hlam]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10012, hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10017, hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10809, hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10813, hlam, p10953_1]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10013, hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10018, hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10810, hlam, p10953_0]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [h10008, h10015, h10016, h10810, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10953_1]
                      · have p10953_0 := h10953c.1
                        have p10953_1 := h10953c.2.1
                        have p10953_2 := h10953c.2.2.1
                        have p10953_3 := h10953c.2.2.2
                        linarith only [hlam, p10953_0]
                · linarith only [h10810, h10948, hlam]
              · linarith only [h10016, h10947, hlam]
            · linarith only [h10011, h10946, hlam]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [h10010, hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [h10015, h8410, hc01, hc24, hlam, hphi, ht12, p10815_1]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [h10809, hlam, p10815_1]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [h10811, hlam, p10815_1]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [h10011, hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [h10016, hlam, p10815_0]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [h10810, hlam, p10815_1]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [h10008, h10015, h10016, h8410, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10815_1]
          · have p10815_0 := h10815c.1
            have p10815_1 := h10815c.2.1
            have p10815_2 := h10815c.2.2.1
            have p10815_3 := h10815c.2.2.2
            linarith only [hlam, p10815_0]
    · linarith only [h10008, h10015, h10018, h10809, h10810, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h11054 | h11054
    · linarith only [h10012, h10014, h10015, h10017, h10019, h10809, h11054, h8410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h11056 | h11056
      · linarith only [h0, h10010, h10017, h10019, h10809, h11056, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h11058 | h11058
        · linarith only [h10017, h10019, h11058, hlam]
        · rcases h2bigk with h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c | h11060c
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h0, hlam, p11060_1]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10009, h10012, h10014, h10017, h10019, h10809, hlam, p11060_2]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            rcases p11060_3 (m.d 0 2) (by simp) with h11064 | h11064
            · rcases p11060_3 (m.d 1 2) (by simp) with h11065 | h11065
              · rcases p11060_3 (m.d 2 3) (by simp) with h11066 | h11066
                · linarith only [h10009, h11066, hlam]
                · rcases p11060_3 (m.d 2 4) (by simp) with h11068 | h11068
                  · linarith only [h11068, hlam, p11060_0]
                  · rcases p11060_3 (m.d 2 5) (by simp) with h11070 | h11070
                    · linarith only [h10011, h11070, hlam]
                    · linarith only [h11056, h11070, hlam]
              · linarith only [h0, h10009, h10012, h10014, h10017, h10019, h10809, h11054, h11056, h11065, hc23, hc35, hlam, hphi]
            · linarith only [h11064, hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            rcases p11060_3 (m.d 0 2) (by simp) with h11075 | h11075
            · rcases p11060_3 (m.d 1 2) (by simp) with h11076 | h11076
              · rcases p11060_3 (m.d 2 3) (by simp) with h11077 | h11077
                · linarith only [h10009, h11077, hlam]
                · rcases p11060_3 (m.d 2 4) (by simp) with h11079 | h11079
                  · linarith only [h10010, h11079, hlam]
                  · rcases p11060_3 (m.d 2 5) (by simp) with h11081 | h11081
                    · linarith only [h11081, hlam, p11060_0]
                    · rcases h3bigk with h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c | h11083c
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h8410, hlam, p11083_1]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10012, h10014, h10017, h10019, h10809, hlam, p11083_2]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        rcases p11083_3 (m.d 0 3) (by simp) with h11087 | h11087
                        · rcases p11083_3 (m.d 1 3) (by simp) with h11088 | h11088
                          · rcases p11083_3 (m.d 2 3) (by simp) with h11089 | h11089
                            · linarith only [h10009, h11089, hlam]
                            · rcases p11083_3 (m.d 3 4) (by simp) with h11091 | h11091
                              · linarith only [h11091, hlam, p11083_0]
                              · rcases p11083_3 (m.d 3 5) (by simp) with h11093 | h11093
                                · linarith only [h10013, h11093, hlam]
                                · linarith only [h11058, h11093, hlam]
                          · linarith only [h10017, h11088, hlam]
                        · linarith only [h11087, hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        rcases p11083_3 (m.d 0 3) (by simp) with h11098 | h11098
                        · rcases p11083_3 (m.d 1 3) (by simp) with h11099 | h11099
                          · rcases p11083_3 (m.d 2 3) (by simp) with h11100 | h11100
                            · linarith only [h10009, h11100, hlam]
                            · rcases p11083_3 (m.d 3 4) (by simp) with h11102 | h11102
                              · linarith only [h10012, h11102, hlam]
                              · rcases p11083_3 (m.d 3 5) (by simp) with h11104 | h11104
                                · linarith only [h11104, hlam, p11083_0]
                                · rcases h5bigk with h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c | h11106c
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [hlam, p11106_0]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h0, h10008, h10018, h11054, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h0, h10008, h10009, h10012, h10014, h10017, h10019, h10809, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11060_2, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h0, h10008, h10009, h10012, h10014, h10017, h10019, h10809, h11054, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11060_2, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h0, h10008, h10017, h10019, h10809, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10008, hlam, p11106_0]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [hlam, p11106_0]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10008, h10009, h10012, h10014, h10015, h10017, h10019, h10809, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11060_2, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10008, h10009, h10012, h10014, h10015, h10017, h10019, h10809, h11054, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11060_2, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10019, hlam, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10011, hlam, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10016, hlam, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [hlam, p11106_0]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h11054, hlam, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h11056, hlam, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10013, hlam, p11106_0]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10018, hlam, p11106_0]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10009, h10012, h10014, h10017, h10019, h10809, hc23, hc35, hlam, hphi, p11060_2, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [hlam, p11106_0]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h11058, hlam, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10014, hlam, p11106_0]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10009, h10012, h10014, hc02, hc15, hlam, hphi, ht0b, ht5b, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h10009, h10012, h10014, hlam, p11060_2, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [h0, h10009, h10012, h10014, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p11106_1]
                                  · have p11106_0 := h11106c.1
                                    have p11106_1 := h11106c.2.1
                                    have p11106_2 := h11106c.2.2.1
                                    have p11106_3 := h11106c.2.2.2
                                    linarith only [hlam, p11106_0]
                          · linarith only [h10018, h11099, hlam]
                        · linarith only [h11098, hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10012, h10014, h10015, h10017, h10019, h10809, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11083_1]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10012, h10014, h10017, h10019, h10809, h8410, hlam, p11083_2]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        rcases p11083_3 (m.d 0 3) (by simp) with h11137 | h11137
                        · linarith only [h11137, h8410, hlam]
                        · linarith only [h10012, h11137, hlam]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        rcases p11083_3 (m.d 0 3) (by simp) with h11140 | h11140
                        · linarith only [h11140, h8410, hlam]
                        · linarith only [h10013, h11140, hlam]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10009, hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10015, hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10809, hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h11054, hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10012, hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10017, hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10012, h10014, h10017, h10019, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11083_1]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h11058, hlam, p11083_1]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10013, hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10018, hlam, p11083_0]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10008, h10015, h10018, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11083_1]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [h10008, h10015, h10018, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11083_1]
                      · have p11083_0 := h11083c.1
                        have p11083_1 := h11083c.2.1
                        have p11083_2 := h11083c.2.2.1
                        have p11083_3 := h11083c.2.2.2
                        linarith only [hlam, p11083_0]
              · linarith only [h10016, h11076, hlam]
            · linarith only [h11075, hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10009, h10012, h10014, h10019, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p11060_1]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h0, h10009, h10012, h10014, h10017, h10019, h10809, hlam, p11060_2]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            rcases p11060_3 (m.d 0 2) (by simp) with h11163 | h11163
            · linarith only [h0, h11163, hlam]
            · linarith only [h10010, h11163, hlam]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            rcases p11060_3 (m.d 0 2) (by simp) with h11166 | h11166
            · linarith only [h0, h11166, hlam]
            · linarith only [h10011, h11166, hlam]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10009, hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10015, hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10809, hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h11054, hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10010, hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10015, h8410, hc01, hc24, hlam, hphi, ht12, p11060_1]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10009, h10012, h10014, h10017, h10019, h10809, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11060_1]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h11056, hlam, p11060_1]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10011, hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10016, hlam, p11060_0]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10008, h10015, h10018, h11054, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11060_1]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [h10008, h10015, h10018, h11054, h8410, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11060_1]
          · have p11060_0 := h11060c.1
            have p11060_1 := h11060c.2.1
            have p11060_2 := h11060c.2.2.1
            have p11060_3 := h11060c.2.2.2
            linarith only [hlam, p11060_0]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10016 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10017 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h10018 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 1 4 5 (by decide) (by decide) with h10019 | h10019
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015 h10016 h10017 h10018 h10019
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015 h10016 h10017 h10018 h10019

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10016 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10017 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h10018 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  linarith only [h10018, h8410, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10016 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10017 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 1 3 5 (by decide) (by decide) with h10018 | h10018
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015 h10016 h10017 h10018
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015 h10016 h10017 h10018

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10016 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10017 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  linarith only [h10008, h10017, h8410, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10016 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 1 3 4 (by decide) (by decide) with h10017 | h10017
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015 h10016 h10017
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015 h10016 h10017

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10016 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  linarith only [h10008, h10015, h10016, h8410, hc25, hlam, hphi, ht01, ht12, u0ehi4]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 1 2 5 (by decide) (by decide) with h10016 | h10016
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015 h10016
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015 h10016

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  linarith only [h0, h10008, h10015, hc23, hlam, hphi, ht01, ht12, u0ehi4]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 1 2 3 (by decide) (by decide) with h10015 | h10015
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h10009 h10010 h10011 h10012 h10013 h10014 h10015

end R2N4
