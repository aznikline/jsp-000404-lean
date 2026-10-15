import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h833 | h833
  · rcases m.htr 0 2 5 (by decide) (by decide) with h834 | h834
    · rcases m.htr 0 3 4 (by decide) (by decide) with h835 | h835
      · rcases m.htr 0 3 5 (by decide) (by decide) with h836 | h836
        · rcases m.htr 0 4 5 (by decide) (by decide) with h837 | h837
          · rcases m.htr 1 2 3 (by decide) (by decide) with h838 | h838
            · linarith only [h4, h838, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
              · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                · rcases m.htr 1 4 5 (by decide) (by decide) with h842 | h842
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h843 | h843
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h844 | h844
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h845 | h845
                        · linarith only [h4, h833, h843, h845, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · linarith only [h2, h4, h833, h842, h845, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h3, h4, h833, h841, h844, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h4, h833, h835, h843, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h4, h833, h837, h840, h842, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h4, h833, h836, h837, h838, h841, hc12, hlam, hphi, u2elo2]
              · linarith only [h4, h835, h838, h840, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h853 | h853
            · linarith only [h4, h853, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h855 | h855
              · rcases m.htr 1 3 5 (by decide) (by decide) with h856 | h856
                · rcases m.htr 1 4 5 (by decide) (by decide) with h857 | h857
                  · linarith only [h2, h837, h857, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h859 | h859
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h860 | h860
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h861 | h861
                        · linarith only [h2, h4, h833, h837, h859, h861, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · rcases h0bigk with h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c | h863c
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h834, hc01, hc25, hlam, hphi, ht0b, ht5b, p863_1]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h4, h834, h860, hc01, hc35, hlam, hphi, ht0b, ht5b, p863_1]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            rcases p863_3 (m.d 0 1) (by simp) with h867 | h867
                            · rcases p863_3 (m.d 0 2) (by simp) with h868 | h868
                              · linarith only [h0, h868, hlam]
                              · linarith only [h833, h868, hlam]
                            · linarith only [h2, h867, hlam]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            rcases p863_3 (m.d 0 1) (by simp) with h872 | h872
                            · rcases p863_3 (m.d 0 2) (by simp) with h873 | h873
                              · linarith only [h0, h873, hlam]
                              · linarith only [h834, h873, hlam]
                            · linarith only [h3, h872, hlam]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h0, hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h4, hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h4, h833, h859, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p863_1, u2elo2]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h4, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p863_1, u2elo2]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h1, hlam, p863_1]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p863_1, u2elo2]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h4, h833, h859, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p863_1, u2elo2]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h4, h834, h860, h861, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p863_1, u2elo2]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h2, hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h833, hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h835, hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h837, hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h3, hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h834, hlam, p863_1]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h836, hlam, p863_0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [h833, h834, h859, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p863_1, u2elo0]
                          · have p863_0 := h863c.1
                            have p863_1 := h863c.2.1
                            have p863_2 := h863c.2.2.1
                            have p863_3 := h863c.2.2.2
                            linarith only [hlam, p863_0]
                      · linarith only [h4, h836, h860, hlam]
                    · linarith only [h3, h4, h834, h855, h857, h859, hlam]
                · linarith only [h4, h834, h836, h853, h856, hc12, hlam, hphi, u2elo2]
              · linarith only [h4, h835, h853, h855, hc12, hlam, hphi, u2elo2]
        · linarith only [h4, h834, h836, hlam]
      · linarith only [h4, h833, h835, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h903 | h903
      · rcases m.htr 0 3 5 (by decide) (by decide) with h904 | h904
        · rcases m.htr 0 4 5 (by decide) (by decide) with h905 | h905
          · linarith only [h833, h834, h905, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h907 | h907
            · linarith only [h4, h907, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h909 | h909
              · rcases m.htr 1 3 5 (by decide) (by decide) with h910 | h910
                · rcases m.htr 1 4 5 (by decide) (by decide) with h911 | h911
                  · linarith only [h2, h833, h834, h905, h911, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h913 | h913
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h914 | h914
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h915 | h915
                        · linarith only [h833, h834, h905, h913, h914, h915, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · rcases h0bigk with h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c | h917c
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h833, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h833, h834, h904, h913, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            rcases p917_3 (m.d 0 1) (by simp) with h921 | h921
                            · rcases p917_3 (m.d 0 2) (by simp) with h922 | h922
                              · linarith only [h0, h922, hlam]
                              · linarith only [h833, h922, hlam]
                            · linarith only [h2, h921, hlam]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h833, h834, h913, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h0, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h4, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h833, h834, h913, h914, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p917_1, u2elo2]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h834, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h1, hlam, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p917_1, u2elo2]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h4, h833, h913, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p917_1, u2elo2]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h4, h833, h834, h913, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p917_1, u2elo2]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h2, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h833, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h903, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h905, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h3, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h833, h913, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p917_1]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h904, hlam, p917_0]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [h833, h834, h913, h914, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p917_1, u2elo2]
                          · have p917_0 := h917c.1
                            have p917_1 := h917c.2.1
                            have p917_2 := h917c.2.2.1
                            have p917_3 := h917c.2.2.2
                            linarith only [hlam, p917_0]
                      · linarith only [h1, h4, h910, h914, hlam]
                    · linarith only [h2, h4, h833, h909, h913, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h4, h904, h907, h910, hc12, hlam, hphi, u2elo2]
              · linarith only [h4, h903, h907, h909, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h951 | h951
          · linarith only [h4, h833, h904, h951, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h953 | h953
            · linarith only [h0, h4, h953, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h955 | h955
              · rcases m.htr 1 3 5 (by decide) (by decide) with h956 | h956
                · linarith only [h1, h904, h956, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h958 | h958
                  · linarith only [h2, h4, h833, h904, h951, h958, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h960 | h960
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h961 | h961
                      · linarith only [h4, h904, h961, hc02, hlam, hphi, u2elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h963 | h963
                        · linarith only [h3, h951, h955, h956, h963, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h4, h833, h961, h963, hc24, hc45, hlam, hphi]
                    · linarith only [h2, h4, h833, h955, h960, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h903, h904, h955, hc13, hc35, hlam, hphi]
      · linarith only [h4, h833, h903, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h969 | h969
    · rcases m.htr 0 3 4 (by decide) (by decide) with h970 | h970
      · rcases m.htr 0 3 5 (by decide) (by decide) with h971 | h971
        · rcases m.htr 0 4 5 (by decide) (by decide) with h972 | h972
          · rcases m.htr 1 2 3 (by decide) (by decide) with h973 | h973
            · linarith only [h4, h973, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h975 | h975
              · rcases m.htr 1 3 5 (by decide) (by decide) with h976 | h976
                · rcases m.htr 1 4 5 (by decide) (by decide) with h977 | h977
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h978 | h978
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h979 | h979
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h980 | h980
                        · rcases h0bigk with h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [hlam, p981_0]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h969, h979, h980, hc01, hc45, hlam, hphi, ht0b, ht5b, p981_1]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h1, h975, h980, hc01, hc45, hlam, hphi, ht0b, ht5b, p981_1]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h833, h969, h979, h980, hc01, hc45, hlam, hphi, ht0b, ht5b, p981_1]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            rcases p981_3 (m.d 0 1) (by simp) with h986 | h986
                            · rcases p981_3 (m.d 0 2) (by simp) with h987 | h987
                              · linarith only [h0, h987, hlam]
                              · linarith only [h969, h987, hlam]
                            · linarith only [h3, h986, hlam]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h0, hlam, p981_0]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [hlam, p981_0]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h4, hlam, p981_0]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h833, hlam, p981_1]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h3, h833, h978, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p981_1, u2elo2]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h1, hlam, p981_1]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h4, hc02, hlam, hphi, p981_1, u2elo2]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [hlam, p981_0]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h4, h833, h969, h979, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p981_1, u2elo2]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h4, h969, h979, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p981_1, u2elo2]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h2, hlam, p981_0]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h969, h979, hc04, hc35, hlam, hphi, ht0b, ht5b, p981_1]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h970, hlam, p981_0]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [hlam, p981_0]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h833, h969, h978, h979, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p981_1, u2elo2]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h3, hlam, p981_0]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h969, hlam, p981_1]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h971, hlam, p981_0]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [h972, hlam, p981_1]
                          · have p981_0 := h981c.1
                            have p981_1 := h981c.2.1
                            have p981_2 := h981c.2.2.1
                            have p981_3 := h981c.2.2.2
                            linarith only [hlam, p981_0]
                        · rcases h0bigk with h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [hlam, p1011_0]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h3, h969, h977, h980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1011_1]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h3, h4, h969, h977, h980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1011_1]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h3, h833, h969, h977, h980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1011_1]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h3, h977, h980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1011_1]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h0, hlam, p1011_0]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [hlam, p1011_0]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h4, hlam, p1011_0]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h833, hlam, p1011_1]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h3, h977, h980, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1011_1]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h1, hlam, p1011_1]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p1011_1, u2elo2]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [hlam, p1011_0]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h3, h4, h833, h969, h977, h980, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1011_1, u2elo2]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h3, h4, h977, h980, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1011_1, u2elo2]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h2, hlam, p1011_0]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h3, h969, h977, h980, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1011_1]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h970, hlam, p1011_0]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [hlam, p1011_0]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h3, h833, h977, h978, h980, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1011_1, u2elo2]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h3, hlam, p1011_0]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h969, hlam, p1011_1]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h971, hlam, p1011_0]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [h972, hlam, p1011_1]
                          · have p1011_0 := h1011c.1
                            have p1011_1 := h1011c.2.1
                            have p1011_2 := h1011c.2.2.1
                            have p1011_3 := h1011c.2.2.2
                            linarith only [hlam, p1011_0]
                      · linarith only [h4, h971, h979, hlam]
                    · linarith only [h4, h970, h978, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1039 | h1039
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1040 | h1040
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1041 | h1041
                        · linarith only [h1041, h975, h977, hlam]
                        · rcases h0bigk with h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [hlam, p1043_0]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h969, h972, h975, h977, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1043_1]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h4, h969, h972, h975, h977, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1043_1]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h833, h969, h972, h975, h977, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1043_1]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h972, h975, h977, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1043_1]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h0, hlam, p1043_0]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [hlam, p1043_0]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h4, hlam, p1043_0]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h833, hlam, p1043_1]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h972, h975, h977, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1043_1]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h1, hlam, p1043_1]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h969, hc03, hc25, hlam, hphi, ht0b, ht5b, p1043_1]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [hlam, p1043_0]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h4, h833, h969, h972, h975, h977, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1043_1, u2elo2]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h4, h972, h975, h977, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1043_1, u2elo2]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h2, hlam, p1043_0]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h969, h972, h975, h977, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1043_1]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h970, hlam, p1043_0]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [hlam, p1043_0]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h4, h970, h972, h975, h977, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1043_1, u2elo2]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h3, hlam, p1043_0]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h969, hlam, p1043_1]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h971, hlam, p1043_0]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [h972, hlam, p1043_1]
                          · have p1043_0 := h1043c.1
                            have p1043_1 := h1043c.2.1
                            have p1043_2 := h1043c.2.2.1
                            have p1043_3 := h1043c.2.2.2
                            linarith only [hlam, p1043_0]
                      · linarith only [h1040, h4, h971, hlam]
                    · linarith only [h1039, h2, h4, h970, h975, hlam]
                · linarith only [h4, h971, h975, h976, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h4, h970, h973, h975, hc12, hlam, hphi, u2elo2]
          · linarith only [h833, h969, h972, hlam]
        · linarith only [h4, h969, h971, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1075 | h1075
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1076 | h1076
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1077 | h1077
            · linarith only [h1077, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1079 | h1079
              · linarith only [h1, h1079, h4, h969, h970, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1081 | h1081
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1082 | h1082
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1083 | h1083
                    · linarith only [h1083, h4, h969, h970, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1085 | h1085
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1086 | h1086
                        · rcases h0bigk with h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [hlam, p1087_0]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h1085, h1086, h969, hc01, hc45, hlam, hphi, ht0b, ht5b, p1087_1]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h1085, h1086, h4, h969, hc01, hc45, hlam, hphi, ht0b, ht5b, p1087_1]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h1085, h1086, h4, h969, h970, hc01, hc45, hlam, hphi, ht0b, ht5b, p1087_1]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            rcases p1087_3 (m.d 0 1) (by simp) with h1092 | h1092
                            · rcases p1087_3 (m.d 0 2) (by simp) with h1093 | h1093
                              · linarith only [h0, h1093, hlam]
                              · linarith only [h1093, h969, hlam]
                            · linarith only [h1092, h3, hlam]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h0, hlam, p1087_0]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [hlam, p1087_0]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h4, hlam, p1087_0]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h833, hlam, p1087_1]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1087_1, u2elo0]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h1, hlam, p1087_1]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h0, h1083, h4, hc12, hc34, hlam, hphi, ht23, p1087_1]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [hlam, p1087_0]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h970, hlam, p1087_1]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h1083, h1085, h1086, h4, h969, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1087_1]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h2, hlam, p1087_0]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h1085, h1086, h833, h969, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1087_1, u2elo3]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h833, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1087_1, u2elo3]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [hlam, p1087_0]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h1085, h1086, h833, h969, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1087_1, u2elo3]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h3, hlam, p1087_0]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h969, hlam, p1087_1]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h1075, hlam, p1087_0]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [h1076, hlam, p1087_1]
                          · have p1087_0 := h1087c.1
                            have p1087_1 := h1087c.2.1
                            have p1087_2 := h1087c.2.2.1
                            have p1087_3 := h1087c.2.2.2
                            linarith only [hlam, p1087_0]
                        · linarith only [h1083, h1085, h1086, h4, h969, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h1081, h1085, h4, h969, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h1076, h1077, h1079, h1082, h4, h969, hc12, hlam, hphi, u2elo2]
                · linarith only [h1075, h1077, h1081, h970, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1076, h4, h969, h970, hlam]
        · linarith only [h1075, h4, h969, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1123 | h1123
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1124 | h1124
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1125 | h1125
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1126 | h1126
            · linarith only [h1126, h4, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1128 | h1128
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1129 | h1129
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1130 | h1130
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1131 | h1131
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1132 | h1132
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1133 | h1133
                        · rcases h0bigk with h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [hlam, p1134_0]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            rcases p1134_3 (m.d 0 1) (by simp) with h1136 | h1136
                            · rcases p1134_3 (m.d 0 2) (by simp) with h1137 | h1137
                              · linarith only [h0, h1137, hlam]
                              · rcases p1134_3 (m.d 0 3) (by simp) with h1139 | h1139
                                · linarith only [h1, h1139, hlam]
                                · linarith only [h1139, h4, hlam]
                            · linarith only [h0, h1136, hlam]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h1, h1128, h1133, hc01, hc45, hlam, hphi, ht0b, ht5b, p1134_1]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h1128, h1133, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1134_1]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            rcases p1134_3 (m.d 0 1) (by simp) with h1145 | h1145
                            · rcases p1134_3 (m.d 0 2) (by simp) with h1146 | h1146
                              · linarith only [h0, h1146, hlam]
                              · rcases p1134_3 (m.d 0 3) (by simp) with h1148 | h1148
                                · linarith only [h1, h1148, hlam]
                                · linarith only [h1124, h1148, hlam]
                            · linarith only [h1145, h3, hlam]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h0, hlam, p1134_0]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [hlam, p1134_0]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h4, hlam, p1134_0]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h833, hlam, p1134_1]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h969, hlam, p1134_0]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h1, hlam, p1134_1]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p1134_1, u2elo2]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [hlam, p1134_0]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h1128, h1133, h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1134_1, u2elo2]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h0, h4, h969, hc12, hlam, hphi, p1134_1, u2elo2]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h2, hlam, p1134_0]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h0, h1131, h833, hc12, hlam, hphi, p1134_1, u2elo2]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h1123, hlam, p1134_0]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [hlam, p1134_0]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h0, h1131, h833, h969, hc12, hlam, hphi, p1134_1, u2elo2]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h3, hlam, p1134_0]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h0, h969, hc12, hlam, hphi, p1134_1, u2elo4]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h1124, hlam, p1134_0]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [h1125, hlam, p1134_1]
                          · have p1134_0 := h1134c.1
                            have p1134_1 := h1134c.2.1
                            have p1134_2 := h1134c.2.2.1
                            have p1134_3 := h1134c.2.2.2
                            linarith only [hlam, p1134_0]
                        · rcases h0bigk with h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [hlam, p1172_0]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            rcases p1172_3 (m.d 0 1) (by simp) with h1174 | h1174
                            · rcases p1172_3 (m.d 0 2) (by simp) with h1175 | h1175
                              · linarith only [h0, h1175, hlam]
                              · rcases p1172_3 (m.d 0 3) (by simp) with h1177 | h1177
                                · linarith only [h1, h1177, hlam]
                                · linarith only [h1177, h4, hlam]
                            · linarith only [h0, h1174, hlam]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h1, h1128, h1130, h1133, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1172_1]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h1130, h1133, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1172_1]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h1125, h1133, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1172_1]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h0, hlam, p1172_0]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [hlam, p1172_0]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h4, hlam, p1172_0]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h833, hlam, p1172_1]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h969, hlam, p1172_0]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h1, hlam, p1172_1]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p1172_1, u2elo2]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [hlam, p1172_0]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h1130, h1133, h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1172_1, u2elo2]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h0, h4, h969, hc12, hlam, hphi, p1172_1, u2elo2]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h2, hlam, p1172_0]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h0, h1131, h833, hc12, hlam, hphi, p1172_1, u2elo2]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h1123, hlam, p1172_0]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [hlam, p1172_0]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h0, h1131, h833, h969, hc12, hlam, hphi, p1172_1, u2elo2]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h3, hlam, p1172_0]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h0, h1132, h969, hc12, hlam, hphi, p1172_1, u2elo2]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h1124, hlam, p1172_0]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [h1125, hlam, p1172_1]
                          · have p1172_0 := h1172c.1
                            have p1172_1 := h1172c.2.1
                            have p1172_2 := h1172c.2.2.1
                            have p1172_3 := h1172c.2.2.2
                            linarith only [hlam, p1172_0]
                      · linarith only [h1, h1129, h1132, h4, hlam]
                    · linarith only [h1123, h1131, h4, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1206 | h1206
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1207 | h1207
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1208 | h1208
                        · linarith only [h1128, h1130, h1208, hlam]
                        · rcases h0bigk with h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c | h1210c
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [hlam, p1210_0]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            rcases p1210_3 (m.d 0 1) (by simp) with h1212 | h1212
                            · rcases p1210_3 (m.d 0 2) (by simp) with h1213 | h1213
                              · linarith only [h0, h1213, hlam]
                              · rcases p1210_3 (m.d 0 3) (by simp) with h1215 | h1215
                                · linarith only [h1, h1215, hlam]
                                · linarith only [h1215, h4, hlam]
                            · linarith only [h0, h1212, hlam]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h1123, h1125, h1130, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1210_1]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h1125, h1128, h1130, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1210_1]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h1125, h1128, h1130, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1210_1]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h0, hlam, p1210_0]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [hlam, p1210_0]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h4, hlam, p1210_0]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h833, hlam, p1210_1]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h969, hlam, p1210_0]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h1, hlam, p1210_1]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p1210_1, u2elo2]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [hlam, p1210_0]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h1125, h1128, h1130, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1210_1, u2elo2]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h0, h4, h969, hc12, hlam, hphi, p1210_1, u2elo2]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h2, hlam, p1210_0]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h0, h1206, h833, hc12, hlam, hphi, p1210_1, u2elo2]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h1123, hlam, p1210_0]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [hlam, p1210_0]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h0, h1206, h833, h969, hc12, hlam, hphi, p1210_1, u2elo2]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h3, hlam, p1210_0]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h0, h1207, h969, hc12, hlam, hphi, p1210_1, u2elo2]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h1124, hlam, p1210_0]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [h1125, hlam, p1210_1]
                          · have p1210_0 := h1210c.1
                            have p1210_1 := h1210c.2.1
                            have p1210_2 := h1210c.2.2.1
                            have p1210_3 := h1210c.2.2.2
                            linarith only [hlam, p1210_0]
                      · linarith only [h1, h1125, h1129, h1130, h1206, h1207, h833, hc01, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1123, h1125, h1128, h1130, h1206, h4, hlam]
                · linarith only [h1124, h1128, h1129, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h1123, h1126, h1128, h4, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1246 | h1246
            · linarith only [h0, h1246, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1248 | h1248
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1249 | h1249
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1250 | h1250
                  · linarith only [h1125, h1250, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1252 | h1252
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1253 | h1253
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1254 | h1254
                        · linarith only [h0, h1, h1125, h1248, h1254, h833, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h0bigk with h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            rcases p1256_3 (m.d 0 1) (by simp) with h1258 | h1258
                            · rcases p1256_3 (m.d 0 2) (by simp) with h1259 | h1259
                              · linarith only [h0, h1259, hlam]
                              · rcases p1256_3 (m.d 0 3) (by simp) with h1261 | h1261
                                · linarith only [h1, h1261, hlam]
                                · linarith only [h1261, h4, hlam]
                            · linarith only [h0, h1258, hlam]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h1, h1249, hc01, hc35, hlam, hphi, ht0b, ht5b, p1256_1]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            rcases p1256_3 (m.d 0 1) (by simp) with h1266 | h1266
                            · rcases p1256_3 (m.d 0 2) (by simp) with h1267 | h1267
                              · linarith only [h0, h1267, hlam]
                              · rcases p1256_3 (m.d 0 3) (by simp) with h1269 | h1269
                                · linarith only [h1, h1269, hlam]
                                · linarith only [h1123, h1269, hlam]
                            · linarith only [h1266, h2, hlam]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            rcases p1256_3 (m.d 0 1) (by simp) with h1273 | h1273
                            · rcases p1256_3 (m.d 0 2) (by simp) with h1274 | h1274
                              · linarith only [h0, h1274, hlam]
                              · rcases p1256_3 (m.d 0 3) (by simp) with h1276 | h1276
                                · linarith only [h1, h1276, hlam]
                                · linarith only [h1124, h1276, hlam]
                            · linarith only [h1273, h3, hlam]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h0, hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h4, hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h833, hlam, p1256_1]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h969, hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h1, hlam, p1256_1]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p1256_1, u2elo2]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h0, h4, h833, hc12, hlam, hphi, p1256_1, u2elo2]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h0, h1125, h4, h833, hc12, hlam, hphi, p1256_1, u2elo2]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h2, hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h0, h1125, hc12, hc45, hlam, hphi, ht23, ht34, p1256_1]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h1123, hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h1125, hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h3, hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h0, h969, hc12, hlam, hphi, p1256_1, u2elo4]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h1124, hlam, p1256_0]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [h1124, h4, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1256_1, u2elo2]
                          · have p1256_0 := h1256c.1
                            have p1256_1 := h1256c.2.1
                            have p1256_2 := h1256c.2.2.1
                            have p1256_3 := h1256c.2.2.2
                            linarith only [hlam, p1256_0]
                      · linarith only [h1, h1249, h1253, h4, hlam]
                    · linarith only [h0, h1248, h1252, h2, h4, h833, hc12, hlam, hphi, u2elo3]
                · linarith only [h1124, h1248, h1249, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h1123, h1246, h1248, h4, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1304 | h1304
          · linarith only [h1123, h1124, h1304, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1306 | h1306
            · linarith only [h0, h1306, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1308 | h1308
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1309 | h1309
                · linarith only [h1, h1124, h1309, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1311 | h1311
                  · linarith only [h1304, h1311, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1313 | h1313
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1314 | h1314
                      · linarith only [h1, h1124, h1308, h1314, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1316 | h1316
                        · linarith only [h0, h1, h1304, h1308, h1316, h833, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h0bigk with h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            rcases p1318_3 (m.d 0 1) (by simp) with h1320 | h1320
                            · rcases p1318_3 (m.d 0 2) (by simp) with h1321 | h1321
                              · linarith only [h0, h1321, hlam]
                              · rcases p1318_3 (m.d 0 3) (by simp) with h1323 | h1323
                                · linarith only [h1, h1323, hlam]
                                · linarith only [h1323, h4, hlam]
                            · linarith only [h0, h1320, hlam]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1123, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1318_1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            rcases p1318_3 (m.d 0 1) (by simp) with h1328 | h1328
                            · rcases p1318_3 (m.d 0 2) (by simp) with h1329 | h1329
                              · linarith only [h0, h1329, hlam]
                              · rcases p1318_3 (m.d 0 3) (by simp) with h1331 | h1331
                                · linarith only [h1, h1331, hlam]
                                · linarith only [h1123, h1331, hlam]
                            · linarith only [h1328, h2, hlam]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1, h1124, h1308, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1318_1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h0, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h4, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h833, hlam, p1318_1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h969, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1, hlam, p1318_1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h0, h1314, h1316, h4, hc12, hc45, hlam, hphi, ht23, ht34, p1318_1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h0, h1314, h1316, h4, h833, hc12, hc45, hlam, hphi, ht23, ht34, p1318_1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1124, hlam, p1318_1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h2, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h0, h833, hc12, hlam, hphi, p1318_1, u2elo3]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1123, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1304, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h3, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h0, h969, hc12, hlam, hphi, p1318_1, u2elo4]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h969, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1318_1, u2elo4]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h0, h833, h969, hc12, hlam, hphi, p1318_1, u2elo4]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [hlam, p1318_0]
                    · linarith only [h0, h1, h1308, h1313, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1123, h1124, h1308, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1358 | h1358
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1359 | h1359
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1360 | h1360
            · linarith only [h0, h1360, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1362 | h1362
              · linarith only [h1, h1123, h1358, h1362, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1364 | h1364
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1365 | h1365
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1366 | h1366
                    · linarith only [h1, h1123, h1364, h1366, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1368 | h1368
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1369 | h1369
                        · rcases h0bigk with h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [hlam, p1370_0]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            rcases p1370_3 (m.d 0 1) (by simp) with h1372 | h1372
                            · rcases p1370_3 (m.d 0 2) (by simp) with h1373 | h1373
                              · linarith only [h0, h1373, hlam]
                              · rcases p1370_3 (m.d 0 3) (by simp) with h1375 | h1375
                                · linarith only [h1, h1375, hlam]
                                · linarith only [h1375, h4, hlam]
                            · linarith only [h0, h1372, hlam]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h1, h1364, h1369, hc01, hc45, hlam, hphi, ht0b, ht5b, p1370_1]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h1, h1123, h1364, h1369, hc01, hc45, hlam, hphi, ht0b, ht5b, p1370_1]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            rcases p1370_3 (m.d 0 1) (by simp) with h1381 | h1381
                            · rcases p1370_3 (m.d 0 2) (by simp) with h1382 | h1382
                              · linarith only [h0, h1382, hlam]
                              · rcases p1370_3 (m.d 0 3) (by simp) with h1384 | h1384
                                · linarith only [h1, h1384, hlam]
                                · linarith only [h1358, h1384, hlam]
                            · linarith only [h1381, h3, hlam]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h0, hlam, p1370_0]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [hlam, p1370_0]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h4, hlam, p1370_0]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h833, hlam, p1370_1]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h969, hlam, p1370_0]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h1, hlam, p1370_1]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h0, h1366, h4, hc12, hc34, hlam, hphi, ht23, p1370_1]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [hlam, p1370_0]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h1123, hlam, p1370_1]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h0, h1366, h4, h969, hc12, hc34, hlam, hphi, ht23, p1370_1]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h2, hlam, p1370_0]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h0, h833, hc12, hlam, hphi, p1370_1, u2elo3]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h833, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1370_1, u2elo3]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [hlam, p1370_0]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h0, h833, h969, hc12, hlam, hphi, p1370_1, u2elo3]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h3, hlam, p1370_0]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h0, h1366, h1368, h969, hc12, hc34, hlam, hphi, ht23, p1370_1]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h1358, hlam, p1370_0]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [h1359, hlam, p1370_1]
                          · have p1370_0 := h1370c.1
                            have p1370_1 := h1370c.2.1
                            have p1370_2 := h1370c.2.2.1
                            have p1370_3 := h1370c.2.2.2
                            linarith only [hlam, p1370_0]
                        · linarith only [h0, h1366, h1369, h4, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h0, h1362, h1364, h1368, h2, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1359, h1362, h1364, h1365, h833, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h1123, h1358, h1360, h1364, h833, hc12, hlam, hphi, u2elo3]
          · linarith only [h1123, h1358, h1359, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1413 | h1413
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1414 | h1414
            · linarith only [h0, h1414, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1416 | h1416
              · linarith only [h1, h1123, h1416, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1418 | h1418
                · linarith only [h1, h1358, h1418, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1420 | h1420
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1421 | h1421
                    · linarith only [h0, h1123, h1421, h4, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1423 | h1423
                      · linarith only [h0, h1358, h1421, h1423, h4, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1425 | h1425
                        · rcases h0bigk with h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [hlam, p1426_0]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            rcases p1426_3 (m.d 0 1) (by simp) with h1428 | h1428
                            · rcases p1426_3 (m.d 0 2) (by simp) with h1429 | h1429
                              · linarith only [h0, h1429, hlam]
                              · rcases p1426_3 (m.d 0 3) (by simp) with h1431 | h1431
                                · linarith only [h1, h1431, hlam]
                                · linarith only [h1431, h4, hlam]
                            · linarith only [h0, h1428, hlam]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            rcases p1426_3 (m.d 0 1) (by simp) with h1435 | h1435
                            · rcases p1426_3 (m.d 0 2) (by simp) with h1436 | h1436
                              · linarith only [h0, h1436, hlam]
                              · rcases p1426_3 (m.d 0 3) (by simp) with h1438 | h1438
                                · linarith only [h1, h1438, hlam]
                                · rcases p1426_3 (m.d 0 4) (by simp) with h1440 | h1440
                                  · linarith only [h1440, h2, hlam]
                                  · linarith only [h1123, h1440, hlam]
                            · linarith only [h1, h1435, hlam]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h1420, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1426_1]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            rcases p1426_3 (m.d 0 1) (by simp) with h1445 | h1445
                            · rcases p1426_3 (m.d 0 2) (by simp) with h1446 | h1446
                              · linarith only [h0, h1446, hlam]
                              · rcases p1426_3 (m.d 0 3) (by simp) with h1448 | h1448
                                · linarith only [h1, h1448, hlam]
                                · rcases p1426_3 (m.d 0 4) (by simp) with h1450 | h1450
                                  · linarith only [h1450, h2, hlam]
                                  · linarith only [h1413, h1450, hlam]
                            · linarith only [h1445, h3, hlam]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h0, hlam, p1426_0]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [hlam, p1426_0]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h4, hlam, p1426_0]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h833, hlam, p1426_1]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h969, hlam, p1426_0]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h1, hlam, p1426_1]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h0, h1423, h1425, h4, hc12, hc34, hlam, hphi, ht23, p1426_1]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [hlam, p1426_0]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h1123, hlam, p1426_1]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h1358, hlam, p1426_1]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h2, hlam, p1426_0]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h0, h833, hc12, hlam, hphi, p1426_1, u2elo3]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h833, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1426_1, u2elo3]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [hlam, p1426_0]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h0, h1358, h4, h833, hc12, hlam, hphi, p1426_1, u2elo3]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h3, hlam, p1426_0]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h0, h969, hc12, hlam, hphi, p1426_1, u2elo4]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h0, h4, h969, hc12, hlam, hphi, p1426_1, u2elo4]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [h1413, hlam, p1426_1]
                          · have p1426_0 := h1426c.1
                            have p1426_1 := h1426c.2.1
                            have p1426_2 := h1426c.2.2.1
                            have p1426_3 := h1426c.2.2.2
                            linarith only [hlam, p1426_0]
                        · linarith only [h0, h1123, h1420, h1425, h2, h4, h833, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1413, h1414, h1416, h1420, h833, hc12, hlam, hphi, u2elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1476 | h1476
            · linarith only [h0, h1476, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1478 | h1478
              · linarith only [h1, h1123, h1478, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1480 | h1480
                · linarith only [h1, h1358, h1480, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1482 | h1482
                  · linarith only [h1413, h1482, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1484 | h1484
                    · linarith only [h0, h1123, h1484, h4, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1486 | h1486
                      · linarith only [h0, h1358, h1484, h1486, h4, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1488 | h1488
                        · rcases h0bigk with h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c | h1489c
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [hlam, p1489_0]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            rcases p1489_3 (m.d 0 1) (by simp) with h1491 | h1491
                            · rcases p1489_3 (m.d 0 2) (by simp) with h1492 | h1492
                              · linarith only [h0, h1492, hlam]
                              · rcases p1489_3 (m.d 0 3) (by simp) with h1494 | h1494
                                · linarith only [h1, h1494, hlam]
                                · linarith only [h1494, h4, hlam]
                            · linarith only [h0, h1491, hlam]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            rcases p1489_3 (m.d 0 1) (by simp) with h1498 | h1498
                            · rcases p1489_3 (m.d 0 2) (by simp) with h1499 | h1499
                              · linarith only [h0, h1499, hlam]
                              · rcases p1489_3 (m.d 0 3) (by simp) with h1501 | h1501
                                · linarith only [h1, h1501, hlam]
                                · rcases p1489_3 (m.d 0 4) (by simp) with h1503 | h1503
                                  · linarith only [h1503, h2, hlam]
                                  · linarith only [h1123, h1503, hlam]
                            · linarith only [h1, h1498, hlam]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            rcases p1489_3 (m.d 0 1) (by simp) with h1507 | h1507
                            · rcases p1489_3 (m.d 0 2) (by simp) with h1508 | h1508
                              · linarith only [h0, h1508, hlam]
                              · rcases p1489_3 (m.d 0 3) (by simp) with h1510 | h1510
                                · linarith only [h1, h1510, hlam]
                                · rcases p1489_3 (m.d 0 4) (by simp) with h1512 | h1512
                                  · linarith only [h1512, h2, hlam]
                                  · rcases p1489_3 (m.d 0 5) (by simp) with h1514 | h1514
                                    · linarith only [h1514, h3, hlam]
                                    · linarith only [h1413, h1514, hlam]
                            · linarith only [h1507, h2, hlam]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            rcases p1489_3 (m.d 0 1) (by simp) with h1518 | h1518
                            · rcases p1489_3 (m.d 0 2) (by simp) with h1519 | h1519
                              · linarith only [h0, h1519, hlam]
                              · rcases p1489_3 (m.d 0 3) (by simp) with h1521 | h1521
                                · linarith only [h1, h1521, hlam]
                                · rcases p1489_3 (m.d 0 4) (by simp) with h1523 | h1523
                                  · linarith only [h1523, h2, hlam]
                                  · rcases p1489_3 (m.d 0 5) (by simp) with h1525 | h1525
                                    · linarith only [h1525, h3, hlam]
                                    · rcases h3bigk with h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1123, h1413, h1476, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1489_1, p1527_1]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h4, hlam, p1527_1]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1123, hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1358, hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1, hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1476, hlam, p1527_1]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1478, hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1480, hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1486, h1488, hc03, hc34, hlam, hphi, p1527_1]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1476, h1486, h1488, hc12, hc34, hlam, hphi, ht23, p1527_1]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1484, hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1486, hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        rcases p1527_3 (m.d 0 3) (by simp) with h1543 | h1543
                                        · linarith only [h1543, hlam, p1527_0]
                                        · rcases p1527_3 (m.d 1 3) (by simp) with h1545 | h1545
                                          · linarith only [h1478, h1545, hlam]
                                          · rcases p1527_3 (m.d 2 3) (by simp) with h1547 | h1547
                                            · linarith only [h1484, h1547, hlam]
                                            · linarith only [h1547, h4, hlam]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        rcases p1527_3 (m.d 0 3) (by simp) with h1550 | h1550
                                        · linarith only [h1123, h1550, hlam]
                                        · linarith only [h1, h1550, hlam]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p1527_1]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1, h1358, h1476, hc12, hc34, hlam, hphi, ht23, p1527_1]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        rcases p1527_3 (m.d 0 3) (by simp) with h1556 | h1556
                                        · linarith only [h1556, hlam, p1527_0]
                                        · rcases p1527_3 (m.d 1 3) (by simp) with h1558 | h1558
                                          · linarith only [h1480, h1558, hlam]
                                          · rcases p1527_3 (m.d 2 3) (by simp) with h1560 | h1560
                                            · linarith only [h1486, h1560, hlam]
                                            · linarith only [h1560, h4, hlam]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        rcases p1527_3 (m.d 0 3) (by simp) with h1563 | h1563
                                        · linarith only [h1358, h1563, hlam]
                                        · linarith only [h1, h1563, hlam]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p1527_1]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [h1488, hlam, p1527_0]
                                      · have p1527_0 := h1527c.1
                                        have p1527_1 := h1527c.2.1
                                        have p1527_2 := h1527c.2.2.1
                                        have p1527_3 := h1527c.2.2.2
                                        linarith only [hlam, p1527_0]
                            · linarith only [h1518, h3, hlam]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h0, hlam, p1489_0]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [hlam, p1489_0]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h4, hlam, p1489_0]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h833, hlam, p1489_1]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h969, hlam, p1489_0]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h1, hlam, p1489_1]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h0, h4, hc12, hlam, hphi, p1489_1, u2elo2]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [hlam, p1489_0]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h1123, hlam, p1489_1]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h1358, hlam, p1489_1]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h2, hlam, p1489_0]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h0, h1413, hc12, hc45, hlam, hphi, ht23, ht34, p1489_1]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h1413, hc03, hc45, hlam, hphi, ht34, p1489_1]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [hlam, p1489_0]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h1413, hlam, p1489_0]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h3, hlam, p1489_0]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h0, h969, hc12, hlam, hphi, p1489_1, u2elo4]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h1, h1476, h969, hc12, hlam, hphi, p1489_1, u2elo4]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [h969, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1489_1, u2elo4]
                          · have p1489_0 := h1489c.1
                            have p1489_1 := h1489c.2.1
                            have p1489_2 := h1489c.2.2.1
                            have p1489_3 := h1489c.2.2.2
                            linarith only [hlam, p1489_0]
                        · linarith only [h0, h1484, h1488, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6948000 in
set_option maxHeartbeats 6948000 in
theorem r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x0_x0 m hb0 hb2 hb3 h0 h1 h2 h3 h4
  · exact r1l7_20_12_13_H_I_L_0_L_I_x0_x0_x0_x0_x1 m hb0 hb2 hb3 h0 h1 h2 h3 h4

end R2N4
