import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_26S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_13_24_L_I_M_IR_s0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h834 | h834
  · rcases m.htr 0 4 5 (by decide) (by decide) with h835 | h835
    · rcases m.htr 1 2 3 (by decide) (by decide) with h836 | h836
      · rcases m.htr 1 2 4 (by decide) (by decide) with h837 | h837
        · rcases m.htr 1 3 4 (by decide) (by decide) with h838 | h838
          · linarith only [h1, h5, h834, h838, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h840 | h840
            · rcases m.htr 1 4 5 (by decide) (by decide) with h841 | h841
              · rcases m.htr 2 3 4 (by decide) (by decide) with h842 | h842
                · linarith only [h3, h5, h842, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h844 | h844
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h845 | h845
                    · linarith only [h0, h837, h845, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h2, h841, h845, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h5, h834, h844, hc23, hc34, hlam, hphi]
              · linarith only [h838, h840, h841, hlam]
            · linarith only [h5, h834, h840, hc13, hc34, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h851 | h851
          · linarith only [h1, h5, h834, h851, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h853 | h853
            · rcases m.htr 1 4 5 (by decide) (by decide) with h854 | h854
              · rcases m.htr 2 3 4 (by decide) (by decide) with h855 | h855
                · linarith only [h4, h5, h836, h837, h855, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h857 | h857
                  · linarith only [h4, h836, h837, h857, hc02, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h5, h834, h857, hc23, hc34, hlam, hphi]
              · linarith only [h5, h835, h836, h837, h854, hc23, hc34, hlam, hphi]
            · linarith only [h5, h834, h853, hc13, hc34, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h862 | h862
        · linarith only [h3, h5, h836, h862, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h864 | h864
          · linarith only [h3, h5, h836, h864, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h866 | h866
            · rcases m.htr 1 4 5 (by decide) (by decide) with h867 | h867
              · rcases m.htr 2 3 4 (by decide) (by decide) with h868 | h868
                · linarith only [h3, h5, h868, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h870 | h870
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h871 | h871
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h872 | h872
                      · rcases h3bigk with h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c | h873c
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h5, hc13, hc34, hlam, hphi, p873_1]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h5, h836, hc12, hc34, hlam, hphi, ht23, p873_1]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h5, hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h5, h872, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p873_1, u4ehi4]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h1, hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h836, hlam, p873_1]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h864, hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h1, h872, hc01, hlam, hphi, ht0b, ht45, ht5b, p873_1, u4ehi4]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h3, hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h3, h5, hc13, hc34, hlam, hphi, p873_1]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h868, hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h3, h872, hc02, hlam, hphi, ht0b, ht45, ht5b, p873_1, u4ehi4]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h1, h866, h872, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p873_1, u4ehi4]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h866, h872, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p873_1, u4ehi4]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h836, hc12, hc34, hlam, hphi, ht23, p873_1]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          rcases p873_3 (m.d 0 3) (by simp) with h893 | h893
                          · linarith only [h5, h893, hlam]
                          · linarith only [h834, h893, hlam]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h834, hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h866, hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h870, hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [h872, hlam, p873_0]
                        · have p873_0 := h873c.1
                          have p873_1 := h873c.2.1
                          have p873_2 := h873c.2.2.1
                          have p873_3 := h873c.2.2.2
                          linarith only [hlam, p873_0]
                      · linarith only [h5, h835, h872, hlam]
                    · linarith only [h3, h5, h836, h862, h866, h867, h871, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h5, h834, h836, h870, hc13, hc34, hlam, hphi]
              · linarith only [h864, h866, h867, hlam]
            · linarith only [h5, h834, h866, hc13, hc34, hlam, hphi]
    · linarith only [h5, h834, h835, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h907 | h907
    · rcases m.htr 1 2 3 (by decide) (by decide) with h908 | h908
      · rcases m.htr 1 2 4 (by decide) (by decide) with h909 | h909
        · rcases m.htr 1 3 4 (by decide) (by decide) with h910 | h910
          · linarith only [h1, h5, h910, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h912 | h912
            · linarith only [h1, h834, h912, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h914 | h914
              · rcases m.htr 2 3 4 (by decide) (by decide) with h915 | h915
                · linarith only [h3, h5, h915, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h917 | h917
                  · linarith only [h1, h834, h908, h917, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h919 | h919
                    · linarith only [h0, h909, h919, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h2, h914, h919, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h922 | h922
                · linarith only [h1, h5, h907, h908, h909, h914, h922, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h924 | h924
                  · linarith only [h5, h834, h907, h908, h910, h914, h924, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h926 | h926
                    · linarith only [h909, h914, h926, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h928 | h928
                      · rcases h3bigk with h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h5, h908, hc23, hc34, hlam, hphi, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h5, hc23, hc34, hlam, hphi, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h5, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h834, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h1, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h1, h5, hc23, hc34, hlam, hphi, p929_1]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h910, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h912, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h3, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h908, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h922, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h924, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          rcases p929_3 (m.d 0 3) (by simp) with h945 | h945
                          · linarith only [h945, hlam, p929_0]
                          · rcases p929_3 (m.d 1 3) (by simp) with h947 | h947
                            · linarith only [h910, h947, hlam]
                            · rcases p929_3 (m.d 2 3) (by simp) with h949 | h949
                              · linarith only [h922, h949, hlam]
                              · rcases p929_3 (m.d 3 4) (by simp) with h951 | h951
                                · rcases p929_3 (m.d 3 5) (by simp) with h952 | h952
                                  · linarith only [h928, h952, hlam]
                                  · linarith only [h834, h952, hlam]
                                · linarith only [h951, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          rcases p929_3 (m.d 0 3) (by simp) with h956 | h956
                          · linarith only [h5, h956, hlam]
                          · linarith only [h1, h956, hlam]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          rcases p929_3 (m.d 0 3) (by simp) with h959 | h959
                          · linarith only [h5, h959, hlam]
                          · linarith only [h3, h959, hlam]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h834, h907, h909, h914, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p929_1, u4ehi2]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          rcases p929_3 (m.d 0 3) (by simp) with h964 | h964
                          · linarith only [h964, hlam, p929_0]
                          · rcases p929_3 (m.d 1 3) (by simp) with h966 | h966
                            · linarith only [h912, h966, hlam]
                            · rcases p929_3 (m.d 2 3) (by simp) with h968 | h968
                              · linarith only [h924, h968, hlam]
                              · rcases p929_3 (m.d 3 4) (by simp) with h970 | h970
                                · rcases p929_3 (m.d 3 5) (by simp) with h971 | h971
                                  · rcases h4bigk with h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [hlam, p972_0]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      rcases p972_3 (m.d 0 4) (by simp) with h974 | h974
                                      · rcases p972_3 (m.d 1 4) (by simp) with h975 | h975
                                        · linarith only [h2, h975, hlam]
                                        · rcases p972_3 (m.d 2 4) (by simp) with h977 | h977
                                          · linarith only [h4, h977, hlam]
                                          · rcases p972_3 (m.d 3 4) (by simp) with h979 | h979
                                            · rcases p972_3 (m.d 4 5) (by simp) with h980 | h980
                                              · linarith only [h907, h980, hlam]
                                              · linarith only [h914, h980, hlam]
                                            · linarith only [h910, h979, hlam]
                                      · linarith only [h2, h974, hlam]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      rcases p972_3 (m.d 0 4) (by simp) with h985 | h985
                                      · rcases p972_3 (m.d 1 4) (by simp) with h986 | h986
                                        · linarith only [h2, h986, hlam]
                                        · linarith only [h909, h986, hlam]
                                      · linarith only [h4, h985, hlam]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h5, hlam, p972_0]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h909, h914, hc04, hlam, hphi, ht0b, ht45, ht5b, p972_1, u4ehi2]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h2, hlam, p972_1]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [hlam, p972_0]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h907, h914, hc05, hlam, hphi, ht0b, ht45, ht5b, p972_1, u4ehi2]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h910, hlam, p972_1]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h914, hlam, p972_0]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h4, hlam, p972_1]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h909, hlam, p972_1]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [hlam, p972_0]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h922, hlam, p972_1]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h926, hlam, p972_0]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h907, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p972_1, u4ehi4]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      rcases p972_3 (m.d 0 4) (by simp) with h1003 | h1003
                                      · linarith only [h1003, h5, hlam]
                                      · linarith only [h1003, h2, hlam]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      rcases p972_3 (m.d 0 4) (by simp) with h1006 | h1006
                                      · linarith only [h1006, h5, hlam]
                                      · linarith only [h1006, h4, hlam]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [hlam, p972_0]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h909, h914, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p972_1, u4ehi2]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h907, hlam, p972_0]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h907, h909, hc04, hlam, hphi, ht0b, ht45, ht5b, p972_1, u4ehi2]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h5, h907, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p972_1, u4ehi2]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [h928, hlam, p972_0]
                                    · have p972_0 := h972c.1
                                      have p972_1 := h972c.2.1
                                      have p972_2 := h972c.2.2.1
                                      have p972_3 := h972c.2.2.2
                                      linarith only [hlam, p972_0]
                                  · linarith only [h971, hlam, p929_0]
                                · linarith only [h5, h970, hlam]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          rcases p929_3 (m.d 0 3) (by simp) with h1018 | h1018
                          · linarith only [h1018, h834, hlam]
                          · linarith only [h1, h1018, hlam]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          rcases p929_3 (m.d 0 3) (by simp) with h1021 | h1021
                          · linarith only [h1021, h834, hlam]
                          · linarith only [h1021, h3, hlam]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [h928, hlam, p929_0]
                        · have p929_0 := h929c.1
                          have p929_1 := h929c.2.1
                          have p929_2 := h929c.2.2.1
                          have p929_3 := h929c.2.2.2
                          linarith only [hlam, p929_0]
                      · linarith only [h5, h907, h928, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1027 | h1027
          · linarith only [h1, h1027, h5, h907, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1029 | h1029
            · linarith only [h0, h1029, h4, h834, h908, h909, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1031 | h1031
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1032 | h1032
                · linarith only [h1, h1032, h4, h5, h834, h908, h909, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1034 | h1034
                  · linarith only [h1034, h4, h834, h908, h909, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1036 | h1036
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1037 | h1037
                      · rcases h3bigk with h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c | h1038c
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h834, h908, hc23, hc35, hlam, hphi, p1038_1]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h834, hc23, hc35, hlam, hphi, p1038_1]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h5, hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h834, hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h1, hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h1, h834, hc23, hc35, hlam, hphi, p1038_1]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h1027, hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h1029, hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h3, hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h908, hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h1032, hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h1034, hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          rcases p1038_3 (m.d 0 3) (by simp) with h1054 | h1054
                          · linarith only [h1054, hlam, p1038_0]
                          · rcases p1038_3 (m.d 1 3) (by simp) with h1056 | h1056
                            · linarith only [h1027, h1056, hlam]
                            · rcases p1038_3 (m.d 2 3) (by simp) with h1058 | h1058
                              · linarith only [h1032, h1058, hlam]
                              · rcases p1038_3 (m.d 3 4) (by simp) with h1060 | h1060
                                · rcases p1038_3 (m.d 3 5) (by simp) with h1061 | h1061
                                  · linarith only [h1037, h1061, hlam]
                                  · linarith only [h1061, h834, hlam]
                                · linarith only [h1060, hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          rcases p1038_3 (m.d 0 3) (by simp) with h1065 | h1065
                          · linarith only [h1065, h5, hlam]
                          · linarith only [h1, h1065, hlam]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          rcases p1038_3 (m.d 0 3) (by simp) with h1068 | h1068
                          · linarith only [h1068, h5, hlam]
                          · linarith only [h1068, h3, hlam]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h834, hc03, hc34, hlam, hphi, p1038_1]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          rcases p1038_3 (m.d 0 3) (by simp) with h1073 | h1073
                          · linarith only [h1073, hlam, p1038_0]
                          · rcases p1038_3 (m.d 1 3) (by simp) with h1075 | h1075
                            · linarith only [h1029, h1075, hlam]
                            · rcases p1038_3 (m.d 2 3) (by simp) with h1077 | h1077
                              · linarith only [h1034, h1077, hlam]
                              · rcases p1038_3 (m.d 3 4) (by simp) with h1079 | h1079
                                · rcases p1038_3 (m.d 3 5) (by simp) with h1080 | h1080
                                  · rcases h4bigk with h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c | h1081c
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [hlam, p1081_0]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h1031, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1081_1, u4ehi4]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h5, h909, hc12, hc34, hlam, hphi, ht23, p1081_1]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h5, hlam, p1081_0]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      rcases p1081_3 (m.d 0 4) (by simp) with h1086 | h1086
                                      · rcases p1081_3 (m.d 1 4) (by simp) with h1087 | h1087
                                        · linarith only [h1087, h2, hlam]
                                        · linarith only [h1031, h1087, hlam]
                                      · linarith only [h1086, hlam, p1081_0]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h2, hlam, p1081_1]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [hlam, p1081_0]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h909, hlam, p1081_0]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h1027, hlam, p1081_1]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1081_1, u4ehi4]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h4, hlam, p1081_1]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p1081_1, u4ehi1]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [hlam, p1081_0]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h1032, hlam, p1081_1]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p1081_1, u4ehi4]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h1031, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1081_1, u4ehi4]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h1031, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1081_1, u4ehi4]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h908, h909, hc23, hc34, hlam, hphi, p1081_1]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [hlam, p1081_0]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      rcases p1081_3 (m.d 0 4) (by simp) with h1105 | h1105
                                      · linarith only [h1105, h5, hlam]
                                      · linarith only [h1105, h907, hlam]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h907, hlam, p1081_0]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h1031, hlam, p1081_0]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h1036, hlam, p1081_0]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [h1037, hlam, p1081_0]
                                    · have p1081_0 := h1081c.1
                                      have p1081_1 := h1081c.2.1
                                      have p1081_2 := h1081c.2.2.1
                                      have p1081_3 := h1081c.2.2.2
                                      linarith only [hlam, p1081_0]
                                  · linarith only [h1080, hlam, p1038_0]
                                · linarith only [h1079, h5, hlam]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          rcases p1038_3 (m.d 0 3) (by simp) with h1115 | h1115
                          · linarith only [h1115, h834, hlam]
                          · linarith only [h1, h1115, hlam]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          rcases p1038_3 (m.d 0 3) (by simp) with h1118 | h1118
                          · linarith only [h1118, h834, hlam]
                          · linarith only [h1118, h3, hlam]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [h1037, hlam, p1038_0]
                        · have p1038_0 := h1038c.1
                          have p1038_1 := h1038c.2.1
                          have p1038_2 := h1038c.2.2.1
                          have p1038_3 := h1038c.2.2.2
                          linarith only [hlam, p1038_0]
                      · linarith only [h1031, h1037, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h1031, h1036, h909, hlam]
              · linarith only [h1031, h5, h907, h908, h909, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1126 | h1126
        · linarith only [h0, h1126, h3, h908, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1128 | h1128
          · linarith only [h1128, h3, h5, h908, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1130 | h1130
            · linarith only [h1130, h3, h834, h908, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1132 | h1132
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1133 | h1133
                · linarith only [h1133, h3, h5, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1135 | h1135
                  · linarith only [h1135, h3, h834, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1137 | h1137
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1138 | h1138
                      · rcases h3bigk with h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h1138, h834, hc13, hc34, hlam, hphi, p1139_1]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h1138, h834, h908, hc12, hc34, hlam, hphi, ht23, p1139_1]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h5, hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h834, hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h1, hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h908, hlam, p1139_1]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h1128, hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h1130, hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h3, hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h1138, h3, h834, hc13, hc34, hlam, hphi, p1139_1]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h1133, hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h1135, hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h3, h908, hc12, hc34, hlam, hphi, ht23, p1139_1]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          rcases p1139_3 (m.d 0 3) (by simp) with h1156 | h1156
                          · linarith only [h1156, h5, hlam]
                          · linarith only [h1, h1156, hlam]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h908, hc12, hc34, hlam, hphi, ht23, p1139_1]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h3, h834, h908, hc12, hc34, hlam, hphi, ht23, p1139_1]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h3, h908, hc12, hc35, hlam, hphi, ht23, p1139_1]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          rcases p1139_3 (m.d 0 3) (by simp) with h1163 | h1163
                          · linarith only [h1163, h834, hlam]
                          · linarith only [h1, h1163, hlam]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h1138, h908, hc12, hc34, hlam, hphi, ht23, p1139_1]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [h1138, hlam, p1139_0]
                        · have p1139_0 := h1139c.1
                          have p1139_1 := h1139c.2.1
                          have p1139_2 := h1139c.2.2.1
                          have p1139_3 := h1139c.2.2.2
                          linarith only [hlam, p1139_0]
                      · linarith only [h1132, h1138, h2, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · linarith only [h1126, h1132, h1137, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1171 | h1171
                · linarith only [h1132, h1171, h3, h5, h907, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1173 | h1173
                  · linarith only [h1173, h3, h834, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1175 | h1175
                    · linarith only [h0, h1132, h1175, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · linarith only [h1126, h1175, h5, h907, hc12, hc34, hlam, hphi, ht23]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1178 | h1178
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1179 | h1179
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1180 | h1180
          · linarith only [h1, h1180, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1182 | h1182
            · linarith only [h1, h1182, h834, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1184 | h1184
              · linarith only [h1184, h2, h907, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1186 | h1186
                · linarith only [h1, h1178, h1186, h5, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1188 | h1188
                  · linarith only [h1, h1178, h1188, h834, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1190 | h1190
                    · linarith only [h0, h1179, h1190, h5, h907, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1192 | h1192
                      · rcases h3bigk with h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h1178, h5, hc23, hc34, hlam, hphi, p1193_1]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h5, hc23, hc34, hlam, hphi, p1193_1]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h5, hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h834, hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h1, hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h1, h5, hc23, hc34, hlam, hphi, p1193_1]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h1180, hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h1182, hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h3, hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h1178, hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h1186, hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h1188, hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          rcases p1193_3 (m.d 0 3) (by simp) with h1209 | h1209
                          · linarith only [h1209, hlam, p1193_0]
                          · rcases p1193_3 (m.d 1 3) (by simp) with h1211 | h1211
                            · linarith only [h1180, h1211, hlam]
                            · rcases p1193_3 (m.d 2 3) (by simp) with h1213 | h1213
                              · linarith only [h1186, h1213, hlam]
                              · rcases p1193_3 (m.d 3 4) (by simp) with h1215 | h1215
                                · rcases p1193_3 (m.d 3 5) (by simp) with h1216 | h1216
                                  · linarith only [h1192, h1216, hlam]
                                  · linarith only [h1216, h834, hlam]
                                · linarith only [h1215, hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          rcases p1193_3 (m.d 0 3) (by simp) with h1220 | h1220
                          · linarith only [h1220, h5, hlam]
                          · linarith only [h1, h1220, hlam]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          rcases p1193_3 (m.d 0 3) (by simp) with h1223 | h1223
                          · linarith only [h1223, h5, hlam]
                          · linarith only [h1223, h3, hlam]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h1179, h1192, h2, h907, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1193_1, u4ehi2]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          rcases p1193_3 (m.d 0 3) (by simp) with h1228 | h1228
                          · linarith only [h1228, hlam, p1193_0]
                          · rcases p1193_3 (m.d 1 3) (by simp) with h1230 | h1230
                            · linarith only [h1182, h1230, hlam]
                            · rcases p1193_3 (m.d 2 3) (by simp) with h1232 | h1232
                              · linarith only [h1188, h1232, hlam]
                              · rcases p1193_3 (m.d 3 4) (by simp) with h1234 | h1234
                                · rcases p1193_3 (m.d 3 5) (by simp) with h1235 | h1235
                                  · rcases h4bigk with h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c | h1236c
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [hlam, p1236_0]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h1179, h907, hc45, hlam, hphi, p1236_1, u4ehi2]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h907, hc45, hlam, hphi, p1236_1, u4ehi2]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h5, hlam, p1236_0]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h907, hlam, p1236_0]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h2, hlam, p1236_1]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [hlam, p1236_0]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1236_1, u4ehi2]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h1180, hlam, p1236_1]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h1184, hlam, p1236_0]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h4, hlam, p1236_1]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h1179, hlam, p1236_1]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [hlam, p1236_0]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h1186, hlam, p1236_1]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h1190, hlam, p1236_0]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      rcases p1236_3 (m.d 0 4) (by simp) with h1252 | h1252
                                      · linarith only [h1252, h5, hlam]
                                      · rcases p1236_3 (m.d 1 4) (by simp) with h1254 | h1254
                                        · linarith only [h1180, h1254, hlam]
                                        · rcases p1236_3 (m.d 2 4) (by simp) with h1256 | h1256
                                          · linarith only [h1186, h1256, hlam]
                                          · rcases p1236_3 (m.d 3 4) (by simp) with h1258 | h1258
                                            · rcases p1236_3 (m.d 4 5) (by simp) with h1259 | h1259
                                              · linarith only [h1192, h1259, hlam]
                                              · linarith only [h1259, h907, hlam]
                                            · linarith only [h1258, h5, hlam]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      rcases p1236_3 (m.d 0 4) (by simp) with h1263 | h1263
                                      · linarith only [h1263, h5, hlam]
                                      · linarith only [h1263, h2, hlam]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      rcases p1236_3 (m.d 0 4) (by simp) with h1266 | h1266
                                      · linarith only [h1266, h5, hlam]
                                      · linarith only [h1266, h4, hlam]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [hlam, p1236_0]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h5, h907, hc03, hc34, hlam, hphi, p1236_1]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h2, hc45, hlam, hphi, p1236_1, u4ehi1]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h1179, hc45, hlam, hphi, p1236_1, u4ehi2]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [hc45, hlam, hphi, p1236_1, u4ehi2]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [h1192, hlam, p1236_0]
                                    · have p1236_0 := h1236c.1
                                      have p1236_1 := h1236c.2.1
                                      have p1236_2 := h1236c.2.2.1
                                      have p1236_3 := h1236c.2.2.2
                                      linarith only [hlam, p1236_0]
                                  · linarith only [h1235, hlam, p1193_0]
                                · linarith only [h1234, h5, hlam]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          rcases p1193_3 (m.d 0 3) (by simp) with h1278 | h1278
                          · linarith only [h1278, h834, hlam]
                          · linarith only [h1, h1278, hlam]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          rcases p1193_3 (m.d 0 3) (by simp) with h1281 | h1281
                          · linarith only [h1281, h834, hlam]
                          · linarith only [h1281, h3, hlam]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [h1192, hlam, p1193_0]
                        · have p1193_0 := h1193c.1
                          have p1193_1 := h1193c.2.1
                          have p1193_2 := h1193c.2.2.1
                          have p1193_3 := h1193c.2.2.2
                          linarith only [hlam, p1193_0]
                      · rcases h3bigk with h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c | h1286c
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1178, h5, hc23, hc34, hlam, hphi, p1286_1]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1192, h5, hc23, hc45, hlam, hphi, ht34, p1286_1]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h5, hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h834, hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1, hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1, h1192, h5, hc23, hc45, hlam, hphi, ht34, p1286_1]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1180, hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1182, hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h3, hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1178, hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1186, hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1188, hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1192, hc03, hc45, hlam, hphi, ht34, p1286_1]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1192, hc13, hc45, hlam, hphi, ht34, p1286_1]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1192, hc23, hc45, hlam, hphi, ht34, p1286_1]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [hlam, p1286_0]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1192, hlam, p1286_1]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          rcases p1286_3 (m.d 0 3) (by simp) with h1307 | h1307
                          · linarith only [h1307, hlam, p1286_0]
                          · rcases p1286_3 (m.d 1 3) (by simp) with h1309 | h1309
                            · linarith only [h1182, h1309, hlam]
                            · rcases p1286_3 (m.d 2 3) (by simp) with h1311 | h1311
                              · linarith only [h1188, h1311, hlam]
                              · rcases p1286_3 (m.d 3 4) (by simp) with h1313 | h1313
                                · linarith only [h1192, h1313, hlam]
                                · linarith only [h1313, h5, hlam]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          rcases p1286_3 (m.d 0 3) (by simp) with h1316 | h1316
                          · linarith only [h1316, h834, hlam]
                          · linarith only [h1, h1316, hlam]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          rcases p1286_3 (m.d 0 3) (by simp) with h1319 | h1319
                          · linarith only [h1319, h834, hlam]
                          · linarith only [h1319, h3, hlam]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [h1192, hc45, hlam, hphi, p1286_1, u4ehi3]
                        · have p1286_0 := h1286c.1
                          have p1286_1 := h1286c.2.1
                          have p1286_2 := h1286c.2.2.1
                          have p1286_3 := h1286c.2.2.2
                          linarith only [hlam, p1286_0]
        · linarith only [h1178, h1179, h4, h907, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1325 | h1325
        · linarith only [h1178, h1325, h3, h5, h907, hc45, hlam, hphi, u4ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1327 | h1327
          · linarith only [h1, h1327, h5, h907, hc45, hlam, hphi, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1329 | h1329
            · linarith only [h1178, h1329, h3, h834, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1331 | h1331
              · linarith only [h1325, h1331, h4, h907, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1333 | h1333
                · linarith only [h1333, h3, h5, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1335 | h1335
                  · linarith only [h1335, h3, h834, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1337 | h1337
                    · linarith only [h1337, h4, h907, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1339 | h1339
                      · linarith only [h1178, h1339, h3, h5, h907, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1178, h1339, h3, h5, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_13_24_L_I_M_IR_s0_x0_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_13_24_L_I_M_IR_s0_x0_x0_x0_x0_x0 m hb3 hb4 hg0 h1 h2 h3 h4 h5
  · exact r1l7_13_24_L_I_M_IR_s0_x0_x0_x0_x0_x1 m hb3 hb4 hg0 h1 h2 h3 h4 h5

set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_13_24_L_I_M_IR_s0_x0_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h1342 | h1342
  · linarith only [h1342, h3, h4, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1344 | h1344
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1345 | h1345
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1346 | h1346
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1347 | h1347
          · linarith only [h0, h1347, h4, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1349 | h1349
            · linarith only [h1, h1342, h1344, h1349, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1351 | h1351
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1352 | h1352
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1353 | h1353
                  · linarith only [h0, h1342, h1346, h1353, h4, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1355 | h1355
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1356 | h1356
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1357 | h1357
                        · linarith only [h1353, h1355, h1357, h3, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h1346, h1353, h1355, h1356, h1357, h4, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1, h1346, h1351, h1352, h1355, h1356, h4, hc03, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1344, h1353, h1355, h3, h4, hc23, hc34, hlam, hphi]
                · linarith only [h1342, h1344, h1345, h1346, h1347, h1352, hc23, hc34, hlam, hphi]
              · linarith only [h1342, h1344, h1351, hc13, hc34, hlam, hphi]
        · linarith only [h1346, h3, h4, hc12, hc24, hlam, hphi]
      · linarith only [h1344, h1345, h3, h4, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1366 | h1366
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1367 | h1367
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1368 | h1368
          · linarith only [h0, h1368, h4, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1370 | h1370
            · linarith only [h1, h1342, h1370, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1372 | h1372
              · linarith only [h1, h1344, h1372, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1374 | h1374
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1375 | h1375
                  · linarith only [h1, h1342, h1375, h3, h4, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1377 | h1377
                    · linarith only [h1, h1344, h1367, h1377, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1379 | h1379
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1380 | h1380
                        · rcases h3bigk with h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c | h1381c
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1344, h1367, hc23, hc35, hlam, hphi, p1381_1]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1375, h3, h4, hc23, hc34, hlam, hphi, p1381_1]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1342, hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1344, hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1, hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1, h1375, h3, h4, hc23, hc34, hlam, hphi, p1381_1]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1370, hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1372, hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h3, hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1367, hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1375, hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1377, hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            rcases p1381_3 (m.d 0 3) (by simp) with h1397 | h1397
                            · linarith only [h1397, hlam, p1381_0]
                            · rcases p1381_3 (m.d 1 3) (by simp) with h1399 | h1399
                              · linarith only [h1370, h1399, hlam]
                              · rcases p1381_3 (m.d 2 3) (by simp) with h1401 | h1401
                                · linarith only [h1375, h1401, hlam]
                                · rcases p1381_3 (m.d 3 4) (by simp) with h1403 | h1403
                                  · rcases p1381_3 (m.d 3 5) (by simp) with h1404 | h1404
                                    · linarith only [h1380, h1404, hlam]
                                    · linarith only [h1344, h1404, hlam]
                                  · linarith only [h1403, hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            rcases p1381_3 (m.d 0 3) (by simp) with h1408 | h1408
                            · linarith only [h1342, h1408, hlam]
                            · linarith only [h1, h1408, hlam]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            rcases p1381_3 (m.d 0 3) (by simp) with h1411 | h1411
                            · linarith only [h1342, h1411, hlam]
                            · linarith only [h1411, h3, hlam]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1344, hc03, hc34, hlam, hphi, p1381_1]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            rcases p1381_3 (m.d 0 3) (by simp) with h1416 | h1416
                            · linarith only [h1416, hlam, p1381_0]
                            · rcases p1381_3 (m.d 1 3) (by simp) with h1418 | h1418
                              · linarith only [h1372, h1418, hlam]
                              · rcases p1381_3 (m.d 2 3) (by simp) with h1420 | h1420
                                · linarith only [h1377, h1420, hlam]
                                · rcases p1381_3 (m.d 3 4) (by simp) with h1422 | h1422
                                  · rcases p1381_3 (m.d 3 5) (by simp) with h1423 | h1423
                                    · rcases h4bigk with h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c | h1424c
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1367, h1368, h1375, h4, hc23, hc34, hlam, hphi, p1424_1]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h4, hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1342, hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        rcases p1424_3 (m.d 0 4) (by simp) with h1429 | h1429
                                        · rcases p1424_3 (m.d 1 4) (by simp) with h1430 | h1430
                                          · linarith only [h1430, h2, hlam]
                                          · linarith only [h1374, h1430, hlam]
                                        · linarith only [h1429, hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h2, hlam, p1424_1]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1368, hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1370, hlam, p1424_1]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p1424_1, u4ehi4]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h0, h1367, h1375, h4, hc23, hc34, hlam, hphi, p1424_1]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1367, h1368, h1375, hc23, hc34, hlam, hphi, p1424_1]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1375, hlam, p1424_1]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        rcases p1424_3 (m.d 0 4) (by simp) with h1443 | h1443
                                        · linarith only [h1443, h4, hlam]
                                        · linarith only [h1366, h1443, hlam]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1374, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1424_1, u4ehi4]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1374, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1424_1, u4ehi4]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h0, h1367, h4, hc23, hc34, hlam, hphi, p1424_1]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        rcases p1424_3 (m.d 0 4) (by simp) with h1450 | h1450
                                        · linarith only [h1342, h1450, hlam]
                                        · linarith only [h1366, h1450, hlam]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1366, hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1374, hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1379, hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [h1380, hlam, p1424_0]
                                      · have p1424_0 := h1424c.1
                                        have p1424_1 := h1424c.2.1
                                        have p1424_2 := h1424c.2.2.1
                                        have p1424_3 := h1424c.2.2.2
                                        linarith only [hlam, p1424_0]
                                    · linarith only [h1423, hlam, p1381_0]
                                  · linarith only [h1342, h1422, hlam]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            rcases p1381_3 (m.d 0 3) (by simp) with h1460 | h1460
                            · linarith only [h1344, h1460, hlam]
                            · linarith only [h1, h1460, hlam]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            rcases p1381_3 (m.d 0 3) (by simp) with h1463 | h1463
                            · linarith only [h1344, h1463, hlam]
                            · linarith only [h1463, h3, hlam]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [h1380, hlam, p1381_0]
                          · have p1381_0 := h1381c.1
                            have p1381_1 := h1381c.2.1
                            have p1381_2 := h1381c.2.2.1
                            have p1381_3 := h1381c.2.2.2
                            linarith only [hlam, p1381_0]
                        · linarith only [h1374, h1380, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h1374, h1379, h2, h4, hlam]
                · linarith only [h1342, h1366, h1367, h1368, h1374, hc23, hc34, hlam, hphi]
        · linarith only [h1367, h3, h4, hc12, hc24, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1472 | h1472
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1473 | h1473
          · linarith only [h0, h1473, h4, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1475 | h1475
            · linarith only [h1, h1342, h1475, h3, h4, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1477 | h1477
              · linarith only [h1, h1344, h1477, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1479 | h1479
                · linarith only [h1366, h1479, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1481 | h1481
                  · linarith only [h0, h1342, h1472, h1481, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1483 | h1483
                    · linarith only [h0, h1344, h1366, h1472, h1483, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1485 | h1485
                      · linarith only [h0, h1366, h1472, h1481, h1485, h4, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h1472, h1485, h4, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h1472, h3, h4, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_13_24_L_I_M_IR_s0_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_13_24_L_I_M_IR_s0_x0_x0_x0_x0 m hb3 hb4 hg0 h1 h2 h3 h4
  · exact r1l7_13_24_L_I_M_IR_s0_x0_x0_x0_x1 m hb3 hb4 hg0 h1 h2 h3 h4

end R2N4
