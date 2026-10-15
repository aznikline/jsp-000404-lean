import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_62S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3116000 in
set_option maxHeartbeats 3116000 in
theorem r1l7_21_14_H_I_L_0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h840 | h840
  · rcases m.htr 0 1 4 (by decide) (by decide) with h841 | h841
    · rcases m.htr 0 1 5 (by decide) (by decide) with h842 | h842
      · rcases m.htr 0 4 5 (by decide) (by decide) with h843 | h843
        · rcases m.htr 1 2 3 (by decide) (by decide) with h844 | h844
          · rcases m.htr 1 2 4 (by decide) (by decide) with h845 | h845
            · rcases m.htr 1 2 5 (by decide) (by decide) with h846 | h846
              · rcases m.htr 1 3 4 (by decide) (by decide) with h847 | h847
                · rcases m.htr 1 3 5 (by decide) (by decide) with h848 | h848
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h849 | h849
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h850 | h850
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h851 | h851
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h852 | h852
                          · linarith only [h0, h840, h844, h850, h852, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h843, h852, hc34, hlam, hphi, u4elo0]
                        · linarith only [h0, h840, h847, h849, h851, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h840, h847, h850, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h843, h849, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h858 | h858
                    · linarith only [h847, h848, h858, hlam]
                    · linarith only [h843, h858, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h861 | h861
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h862 | h862
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h863 | h863
                      · linarith only [h844, h847, h863, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h865 | h865
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h866 | h866
                          · rcases h1bigk with h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, h861, h866, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, h847, h861, h866, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h861, h866, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h847, h861, h866, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              rcases p867_3 (m.d 0 1) (by simp) with h877 | h877
                              · linarith only [h0, h877, hlam]
                              · linarith only [h842, h877, hlam]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h840, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h844, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h847, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h847, h861, h866, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p867_1, u4elo3]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h841, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h845, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, h841, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, h841, h861, h866, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h842, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h846, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h861, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h862, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                          · linarith only [h847, h861, h865, h866, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h843, h865, hc24, hlam, hphi, u4elo0]
                    · linarith only [h843, h862, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h898 | h898
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h899 | h899
                      · linarith only [h844, h847, h899, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h901 | h901
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h902 | h902
                          · rcases h1bigk with h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c | h903c
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h0, hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h0, h844, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p903_1]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h0, h845, h901, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p903_1]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p903_1]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p903_1]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              rcases p903_3 (m.d 0 1) (by simp) with h911 | h911
                              · linarith only [h0, h911, hlam]
                              · linarith only [h840, h911, hlam]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h845, h901, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p903_1]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              rcases p903_3 (m.d 0 1) (by simp) with h915 | h915
                              · linarith only [h0, h915, hlam]
                              · linarith only [h842, h915, hlam]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h840, hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h844, hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h847, hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h861, hlam, p903_1]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h841, hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h845, hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h841, h844, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p903_1]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h0, h841, h844, h861, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p903_1]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h842, hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h846, hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h0, h842, h844, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p903_1]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [h898, hlam, p903_0]
                            · have p903_0 := h903c.1
                              have p903_1 := h903c.2.1
                              have p903_2 := h903c.2.2.1
                              have p903_3 := h903c.2.2.2
                              linarith only [hlam, p903_0]
                          · linarith only [h847, h901, h902, hc14, hlam, hphi, u4elo2]
                        · linarith only [h843, h901, hc24, hlam, hphi, u4elo0]
                    · linarith only [h843, h898, hc14, hlam, hphi, u4elo0]
              · linarith only [h0, h842, h846, hlam]
            · linarith only [h0, h840, h844, h845, hc23, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h840, h844, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h939 | h939
          · rcases m.htr 1 2 4 (by decide) (by decide) with h940 | h940
            · rcases m.htr 1 2 5 (by decide) (by decide) with h941 | h941
              · rcases m.htr 1 3 4 (by decide) (by decide) with h942 | h942
                · rcases m.htr 1 3 5 (by decide) (by decide) with h943 | h943
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h944 | h944
                    · linarith only [h843, h944, hc04, hlam, hphi, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h946 | h946
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h947 | h947
                        · linarith only [h841, h843, h940, h947, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h949 | h949
                          · linarith only [h840, h843, h939, h946, h949, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h1bigk with h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c | h951c
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h0, hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p951_1]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h0, h940, h946, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p951_1]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p951_1]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p951_1]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h943, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p951_1]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              rcases p951_3 (m.d 0 1) (by simp) with h960 | h960
                              · linarith only [h0, h960, hlam]
                              · linarith only [h841, h960, hlam]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              rcases p951_3 (m.d 0 1) (by simp) with h963 | h963
                              · linarith only [h0, h963, hlam]
                              · linarith only [h842, h963, hlam]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h840, hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h939, hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h840, h940, h946, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p951_1]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h0, h840, h940, h944, h946, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p951_1]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h841, hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h940, hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h942, hlam, p951_1]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h944, hlam, p951_1]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h842, hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h941, hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h943, hlam, p951_0]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [h0, h842, h940, h946, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p951_1]
                            · have p951_0 := h951c.1
                              have p951_1 := h951c.2.1
                              have p951_2 := h951c.2.2.1
                              have p951_3 := h951c.2.2.2
                              linarith only [hlam, p951_0]
                      · linarith only [h0, h840, h942, h946, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h982 | h982
                    · linarith only [h841, h843, h982, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h984 | h984
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h985 | h985
                        · linarith only [h841, h843, h940, h985, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h987 | h987
                          · linarith only [h0, h842, h843, h939, h943, h984, h987, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h942, h943, h987, hc34, hlam, hphi, u4elo4]
                      · linarith only [h942, h943, h984, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h991 | h991
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h992 | h992
                    · linarith only [h841, h843, h992, hlam]
                    · linarith only [h942, h991, h992, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h995 | h995
                    · linarith only [h841, h843, h995, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h997 | h997
                      · linarith only [h939, h942, h997, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h999 | h999
                        · linarith only [h841, h843, h940, h999, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1001 | h1001
                          · linarith only [h1001, h843, hc04, hlam, hphi, u4elo3]
                          · linarith only [h1001, h939, h942, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h0, h842, h941, hlam]
            · linarith only [h0, h940, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · linarith only [h0, h840, h939, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1007 | h1007
        · linarith only [h1007, h841, h842, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1009 | h1009
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1010 | h1010
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1011 | h1011
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1012 | h1012
                · linarith only [h1007, h1012, h840, h842, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1014 | h1014
                  · linarith only [h1012, h1014, h841, h842, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1016 | h1016
                    · linarith only [h1007, h1016, h841, h842, hlam]
                    · linarith only [h1012, h1016, h841, h842, hc13, hlam, hphi, ht34, u4elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1019 | h1019
                · linarith only [h0, h1011, h1019, h840, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1021 | h1021
                  · linarith only [h0, h1011, h1019, h1021, h841, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1023 | h1023
                    · linarith only [h0, h1007, h1011, h1023, h841, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1009, h1011, h1019, h1023, h841, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h0, h1009, h1010, h840, hc23, hlam, hphi, ht34, u4elo2]
          · linarith only [h0, h1009, h840, hlam]
    · linarith only [h840, h841, hc13, hlam, hphi, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1029 | h1029
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1030 | h1030
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1031 | h1031
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1032 | h1032
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1033 | h1033
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1034 | h1034
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1035 | h1035
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1036 | h1036
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1037 | h1037
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1038 | h1038
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1039 | h1039
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1040 | h1040
                          · rcases h1bigk with h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h0, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h840, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1033, h1038, h1040, hc01, hc45, hlam, hphi, ht0b, ht5b, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1032, h840, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h840, hc01, hc12, hlam, hphi, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1033, h1038, h1040, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              rcases p1041_3 (m.d 0 1) (by simp) with h1051 | h1051
                              · linarith only [h0, h1051, hlam]
                              · linarith only [h1030, h1051, hlam]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1029, h1033, h1038, h1040, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1032, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1032, h1033, h1038, h1040, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              rcases p1041_3 (m.d 0 1) (by simp) with h1058 | h1058
                              · linarith only [h1058, h840, hlam]
                              · linarith only [h1030, h1058, hlam]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1029, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1033, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1035, hlam, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1029, h1034, h1039, hc01, hc45, hlam, hphi, ht0b, ht5b, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1030, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1034, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1036, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1037, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [hlam, p1041_0]
                          · linarith only [h1031, h1040, hc34, hlam, hphi, u4elo0]
                        · linarith only [h1029, h1032, h1037, h1039, h840, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1073 | h1073
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1074 | h1074
                          · rcases h1bigk with h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c | h1075c
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h0, hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h840, hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1032, h840, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1075_1]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1032, h840, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1075_1]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p1075_1]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h840, hc01, hc12, hlam, hphi, p1075_1]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1033, h1073, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1075_1]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              rcases p1075_3 (m.d 0 1) (by simp) with h1085 | h1085
                              · linarith only [h0, h1085, hlam]
                              · linarith only [h1030, h1085, hlam]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1029, h1035, h1038, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1075_1]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1032, hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1032, h1035, h1038, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1075_1]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              rcases p1075_3 (m.d 0 1) (by simp) with h1092 | h1092
                              · linarith only [h1092, h840, hlam]
                              · linarith only [h1030, h1092, hlam]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1029, hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1033, hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1035, hlam, p1075_1]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1029, h1034, h1073, hc01, hc45, hlam, hphi, ht0b, ht5b, p1075_1]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1030, hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1034, hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1036, hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [h1037, hlam, p1075_0]
                            · have p1075_0 := h1075c.1
                              have p1075_1 := h1075c.2.1
                              have p1075_2 := h1075c.2.2.1
                              have p1075_3 := h1075c.2.2.2
                              linarith only [hlam, p1075_0]
                          · linarith only [h1038, h1074, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h1029, h1032, h1037, h1073, h840, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h1031, h1037, hc14, hlam, hphi, u4elo0]
                  · linarith only [h1030, h1036, h840, hlam]
                · linarith only [h1035, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h1030, h1034, hlam]
            · linarith only [h1032, h1033, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1112 | h1112
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1113 | h1113
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1114 | h1114
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1115 | h1115
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1116 | h1116
                    · linarith only [h0, h1029, h1032, h1116, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1029, h1031, h1032, h1116, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1030, h1032, h1115, hlam]
                · linarith only [h0, h1032, h1114, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h1030, h1113, hlam]
            · linarith only [h0, h1112, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1123 | h1123
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1124 | h1124
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1125 | h1125
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1126 | h1126
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1127 | h1127
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1128 | h1128
                    · linarith only [h1029, h1031, h1128, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1130 | h1130
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1131 | h1131
                        · linarith only [h1029, h1031, h1124, h1131, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1133 | h1133
                          · linarith only [h1029, h1031, h1124, h1130, h1133, hlam]
                          · rcases h1bigk with h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c | h1135c
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h0, hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h840, hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1123, h1124, h1130, h840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1135_1]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1123, h1124, h1128, h1130, h840, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1135_1]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p1135_1]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h840, hc01, hc12, hlam, hphi, p1135_1]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              rcases p1135_3 (m.d 0 1) (by simp) with h1144 | h1144
                              · linarith only [h0, h1144, hlam]
                              · linarith only [h1029, h1144, hlam]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              rcases p1135_3 (m.d 0 1) (by simp) with h1147 | h1147
                              · linarith only [h0, h1147, hlam]
                              · linarith only [h1030, h1147, hlam]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1030, h1124, h1128, h1130, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1135_1]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1123, hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              rcases p1135_3 (m.d 0 1) (by simp) with h1153 | h1153
                              · linarith only [h1153, h840, hlam]
                              · linarith only [h1029, h1153, hlam]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              rcases p1135_3 (m.d 0 1) (by simp) with h1156 | h1156
                              · linarith only [h1156, h840, hlam]
                              · linarith only [h1030, h1156, hlam]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1029, hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1124, hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1126, hlam, p1135_1]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1128, hlam, p1135_1]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1030, hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1125, hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1127, hlam, p1135_0]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [h1030, h1124, h1130, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1135_1]
                            · have p1135_0 := h1135c.1
                              have p1135_1 := h1135c.2.1
                              have p1135_2 := h1135c.2.2.1
                              have p1135_3 := h1135c.2.2.2
                              linarith only [hlam, p1135_0]
                      · linarith only [h1029, h1031, h1126, h1130, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h1030, h1127, h840, hlam]
                · linarith only [h1126, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h1030, h1123, h1125, h840, hlam]
            · linarith only [h1123, h1124, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1174 | h1174
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1175 | h1175
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1176 | h1176
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1177 | h1177
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1178 | h1178
                    · linarith only [h0, h1029, h1123, h1178, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1180 | h1180
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1181 | h1181
                        · linarith only [h0, h1030, h1031, h1123, h1174, h1178, h1181, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1183 | h1183
                          · linarith only [h1029, h1031, h1174, h1180, h1183, hlam]
                          · rcases h1bigk with h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c | h1185c
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [hlam, p1185_0]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h0, hlam, p1185_0]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h840, hlam, p1185_0]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h0, h1123, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1185_1]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h0, h1123, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1185_1]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1123, hc01, hc23, hlam, hphi, ht12, p1185_1]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [hlam, p1185_0]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1123, hlam, p1185_1]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1123, h1174, h1180, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1185_1]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1123, h1175, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1185_1]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1029, h1174, h1180, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1185_1]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h0, h1123, hc02, hc23, hlam, hphi, p1185_1]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [hlam, p1185_0]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              rcases p1185_3 (m.d 0 1) (by simp) with h1199 | h1199
                              · linarith only [h1199, h840, hlam]
                              · linarith only [h1029, h1199, hlam]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              rcases p1185_3 (m.d 0 1) (by simp) with h1202 | h1202
                              · linarith only [h1202, h840, hlam]
                              · linarith only [h1030, h1202, hlam]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1029, hlam, p1185_0]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1174, hlam, p1185_0]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1176, hlam, p1185_1]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [hlam, p1185_0]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1178, hlam, p1185_1]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1030, hlam, p1185_0]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1175, hlam, p1185_0]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1177, hlam, p1185_0]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [h1030, h1174, h1180, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1185_1]
                            · have p1185_0 := h1185c.1
                              have p1185_1 := h1185c.2.1
                              have p1185_2 := h1185c.2.2.1
                              have p1185_3 := h1185c.2.2.2
                              linarith only [hlam, p1185_0]
                      · linarith only [h0, h1030, h1123, h1180, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h1030, h1177, h840, hlam]
                · linarith only [h0, h1123, h1176, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h1030, h1175, hlam]
            · linarith only [h0, h1174, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1220 | h1220
        · linarith only [h1029, h1030, h1220, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1222 | h1222
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1223 | h1223
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1224 | h1224
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1225 | h1225
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1226 | h1226
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1227 | h1227
                    · linarith only [h1029, h1030, h1220, h1222, h1226, h1227, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h1029, h1030, h1227, hc14, hlam, hphi, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1230 | h1230
                    · linarith only [h1220, h1230, hc04, hlam, hphi, u4elo1]
                    · linarith only [h1029, h1223, h1226, h1230, h840, hc24, hlam, hphi, u4elo4]
                · linarith only [h1029, h1223, h1225, h840, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1234 | h1234
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1235 | h1235
                  · linarith only [h1222, h1224, h1235, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1237 | h1237
                    · linarith only [h1029, h1222, h1224, h1237, h840, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h1029, h1222, h1223, h1224, h1237, h840, hc24, hlam, hphi, u4elo4]
                · linarith only [h1029, h1223, h1234, h840, hc24, hlam, hphi, u4elo3]
            · linarith only [h1222, h1223, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1242 | h1242
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1243 | h1243
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1244 | h1244
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1245 | h1245
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1246 | h1246
                    · linarith only [h1029, h1030, h1222, h1243, h1246, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h1029, h1030, h1246, hc14, hlam, hphi, u4elo4]
                  · linarith only [h1222, h1243, h1245, hlam]
                · linarith only [h1029, h1030, h1222, h1242, h1243, h1244, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1251 | h1251
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1252 | h1252
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1253 | h1253
                    · linarith only [h0, h1029, h1222, h1253, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1029, h1243, h1253, hc14, hlam, hphi, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1256 | h1256
                    · linarith only [h0, h1029, h1222, h1252, h1256, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h1029, h1222, h1242, h1252, h1256, hc24, hlam, hphi, u4elo4]
                · linarith only [h0, h1029, h1222, h1242, h1251, hc24, hlam, hphi, u4elo3]
            · linarith only [h0, h1029, h1242, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1261 | h1261
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1262 | h1262
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1263 | h1263
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1264 | h1264
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1265 | h1265
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1266 | h1266
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1267 | h1267
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1268 | h1268
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1269 | h1269
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1270 | h1270
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1271 | h1271
                          · rcases h1bigk with h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c | h1272c
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h0, hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h840, hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1029, hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1029, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1272_1, u4elo1]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p1272_1]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h840, hc01, hc12, hlam, hphi, p1272_1]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1029, h1261, h1265, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1272_1]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              rcases p1272_3 (m.d 0 1) (by simp) with h1282 | h1282
                              · linarith only [h0, h1282, hlam]
                              · linarith only [h1261, h1282, hlam]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1261, h1265, h1270, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1272_1]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1263, hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1029, h1261, h1263, h1265, h1270, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1272_1]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              rcases p1272_3 (m.d 0 1) (by simp) with h1289 | h1289
                              · linarith only [h1289, h840, hlam]
                              · linarith only [h1261, h1289, hlam]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1261, h1265, h1270, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1272_1]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1264, hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1266, hlam, p1272_1]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1265, h1270, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1272_1, u4elo1]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1261, hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1265, hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1267, hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [h1268, hlam, p1272_0]
                            · have p1272_0 := h1272c.1
                              have p1272_1 := h1272c.2.1
                              have p1272_2 := h1272c.2.2.1
                              have p1272_3 := h1272c.2.2.2
                              linarith only [hlam, p1272_0]
                          · linarith only [h1029, h1261, h1265, h1270, h1271, hc34, hlam, hphi, u4elo0]
                        · linarith only [h1262, h1270, hc24, hlam, hphi, u4elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1304 | h1304
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1305 | h1305
                          · rcases h1bigk with h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h0, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h840, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1029, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1029, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1306_1, u4elo1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h840, hc01, hc12, hlam, hphi, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1029, h1261, h1265, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              rcases p1306_3 (m.d 0 1) (by simp) with h1316 | h1316
                              · linarith only [h0, h1316, hlam]
                              · linarith only [h1261, h1316, hlam]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1261, h1265, h1304, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1263, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1029, h1261, h1263, h1265, h1304, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              rcases p1306_3 (m.d 0 1) (by simp) with h1323 | h1323
                              · linarith only [h1323, h840, hlam]
                              · linarith only [h1261, h1323, hlam]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1261, h1265, h1304, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1264, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1266, hlam, p1306_1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1265, h1304, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1306_1, u4elo1]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1261, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1265, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1267, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [h1268, hlam, p1306_0]
                            · have p1306_0 := h1306c.1
                              have p1306_1 := h1306c.2.1
                              have p1306_2 := h1306c.2.2.1
                              have p1306_3 := h1306c.2.2.2
                              linarith only [hlam, p1306_0]
                          · linarith only [h1269, h1305, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h1029, h1261, h1268, h1304, hc24, hlam, hphi, u4elo1]
                    · linarith only [h1029, h1268, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h1029, h1261, h1267, hc13, hlam, hphi, ht34, u4elo1]
                · linarith only [h1266, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h1261, h1265, hlam]
            · linarith only [h1263, h1264, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1343 | h1343
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1344 | h1344
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1345 | h1345
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1346 | h1346
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1347 | h1347
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1348 | h1348
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1349 | h1349
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1350 | h1350
                          · rcases h1bigk with h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h0, hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h840, hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1029, hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1029, h1344, h1349, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1351_1]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1263, hc01, hc23, hlam, hphi, ht12, p1351_1]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1263, hlam, p1351_1]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1029, h1263, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1351_1]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1263, h1344, h1349, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1351_1]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1261, h1263, h1344, h1349, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1351_1]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1263, hc12, hc23, hlam, hphi, p1351_1]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1029, h1261, h1263, h1344, h1349, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1351_1]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              rcases p1351_3 (m.d 0 1) (by simp) with h1366 | h1366
                              · linarith only [h1366, h840, hlam]
                              · linarith only [h1261, h1366, hlam]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1261, h1344, h1349, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1351_1, u4elo1]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1343, hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1345, hlam, p1351_1]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1344, h1349, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1351_1, u4elo1]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1261, hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1344, hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1346, hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [h1347, hlam, p1351_0]
                            · have p1351_0 := h1351c.1
                              have p1351_1 := h1351c.2.1
                              have p1351_2 := h1351c.2.2.1
                              have p1351_3 := h1351c.2.2.2
                              linarith only [hlam, p1351_0]
                          · linarith only [h1029, h1261, h1344, h1349, h1350, hc34, hlam, hphi, u4elo0]
                        · linarith only [h1262, h1348, h1349, hc34, hlam, hphi, u4elo0]
                      · linarith only [h1263, h1348, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h1029, h1261, h1344, h1347, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                  · linarith only [h1029, h1261, h1263, h1343, h1346, hlam]
                · linarith only [h1029, h1261, h1263, h1343, h1344, h1345, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
              · linarith only [h1029, h1261, h1343, h1344, hlam]
            · linarith only [h0, h1343, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h1029, h1261, h1262, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1388 | h1388
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1389 | h1389
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1390 | h1390
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1391 | h1391
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1392 | h1392
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1393 | h1393
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1394 | h1394
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1395 | h1395
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1396 | h1396
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1397 | h1397
                          · rcases h1bigk with h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c | h1398c
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h0, hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h840, hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1029, hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1261, hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p1398_1]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1261, h1392, h1394, hc01, hc12, hlam, hphi, p1398_1]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1261, h1394, hc01, hc12, hlam, hphi, p1398_1]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1261, hc01, hc12, hlam, hphi, p1398_1]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p1398_1]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1389, hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1029, h1389, hc01, hc12, hlam, hphi, p1398_1]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1261, h1389, hc01, hc12, hlam, hphi, p1398_1]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p1398_1]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1390, hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1392, hlam, p1398_1]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1261, hc01, hlam, hphi, ht12, ht23, ht34, p1398_1, u4elo1]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p1398_1]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1391, hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1393, hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [h1394, hlam, p1398_0]
                            · have p1398_0 := h1398c.1
                              have p1398_1 := h1398c.2.1
                              have p1398_2 := h1398c.2.2.1
                              have p1398_3 := h1398c.2.2.2
                              linarith only [hlam, p1398_0]
                          · linarith only [h1388, h1397, hc34, hlam, hphi, u4elo0]
                        · linarith only [h1029, h1388, h1396, hc24, hlam, hphi, u4elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1426 | h1426
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1427 | h1427
                          · rcases h1bigk with h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c | h1428c
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h0, hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h840, hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1029, hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1261, hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p1428_1]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h840, hc01, hc12, hlam, hphi, p1428_1]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1029, hc01, hc12, hlam, hphi, p1428_1]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1261, hc01, hc12, hlam, hphi, p1428_1]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p1428_1]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1389, hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1261, h1389, h1394, hc01, hc12, hlam, hphi, p1428_1]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1261, h1389, hc01, hc12, hlam, hphi, p1428_1]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p1428_1]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1390, hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1392, hlam, p1428_1]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1261, hc01, hlam, hphi, ht12, ht23, ht34, p1428_1, u4elo1]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p1428_1]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1391, hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1393, hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [h1394, hlam, p1428_0]
                            · have p1428_0 := h1428c.1
                              have p1428_1 := h1428c.2.1
                              have p1428_2 := h1428c.2.2.1
                              have p1428_3 := h1428c.2.2.2
                              linarith only [hlam, p1428_0]
                          · linarith only [h1395, h1427, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h1029, h1388, h1426, hc24, hlam, hphi, u4elo1]
                    · linarith only [h1029, h1388, h1394, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1457 | h1457
                    · linarith only [h1392, h1393, h1457, hlam]
                    · linarith only [h1029, h1388, h1457, hlam]
                · linarith only [h1392, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1461 | h1461
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1462 | h1462
                  · linarith only [h1389, h1391, h1462, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1464 | h1464
                    · linarith only [h1389, h1391, h1461, h1464, hlam]
                    · linarith only [h1029, h1388, h1464, hlam]
                · linarith only [h1461, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h1389, h1390, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1469 | h1469
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1470 | h1470
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1471 | h1471
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1472 | h1472
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1473 | h1473
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1474 | h1474
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1475 | h1475
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1476 | h1476
                          · rcases h1bigk with h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c | h1477c
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h0, hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h840, hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1029, hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1261, hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p1477_1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1389, hlam, p1477_1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1029, h1389, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1477_1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1261, h1389, hc01, hc23, hlam, hphi, ht12, p1477_1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1389, hc01, hc23, hlam, hphi, ht12, p1477_1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1389, hc12, hc23, hlam, hphi, p1477_1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1029, h1389, hc01, hc23, hlam, hphi, ht12, p1477_1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1261, h1389, hc01, hc23, hlam, hphi, ht12, p1477_1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p1477_1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1469, hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1471, hlam, p1477_1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1261, hc01, hlam, hphi, ht12, ht23, ht34, p1477_1, u4elo1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p1477_1]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1470, hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1472, hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [h1473, hlam, p1477_0]
                            · have p1477_0 := h1477c.1
                              have p1477_1 := h1477c.2.1
                              have p1477_2 := h1477c.2.2.1
                              have p1477_3 := h1477c.2.2.2
                              linarith only [hlam, p1477_0]
                          · linarith only [h1388, h1476, hc34, hlam, hphi, u4elo0]
                        · linarith only [h1029, h1388, h1475, hc24, hlam, hphi, u4elo1]
                      · linarith only [h1389, h1474, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h1029, h1388, h1473, hlam]
                  · linarith only [h1389, h1470, h1472, hlam]
                · linarith only [h0, h1389, h1471, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1509 | h1509
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1510 | h1510
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1511 | h1511
                    · linarith only [h1469, h1470, h1511, hlam]
                    · linarith only [h1029, h1388, h1511, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1514 | h1514
                    · linarith only [h1389, h1469, h1510, h1514, hlam]
                    · linarith only [h1029, h1388, h1514, hlam]
                · linarith only [h1029, h1389, h1469, h1509, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h0, h1469, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1519 | h1519
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1520 | h1520
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1521 | h1521
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1522 | h1522
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1523 | h1523
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1524 | h1524
                    · linarith only [h1388, h1524, hc04, hlam, hphi, u4elo1]
                    · linarith only [h1029, h1524, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1527 | h1527
                    · linarith only [h1029, h1388, h1522, h1523, h1527, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h1029, h1527, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1522, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1531 | h1531
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1532 | h1532
                  · linarith only [h1519, h1521, h1532, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1534 | h1534
                    · linarith only [h1029, h1388, h1534, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                    · linarith only [h1029, h1534, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1531, h840, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h1519, h1520, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1539 | h1539
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1540 | h1540
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1541 | h1541
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1542 | h1542
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1543 | h1543
                    · linarith only [h1029, h1388, h1519, h1539, h1543, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h1029, h1543, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h1519, h1540, h1542, hlam]
                · linarith only [h1519, h1539, h1541, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1548 | h1548
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1549 | h1549
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1550 | h1550
                    · linarith only [h1029, h1388, h1539, h1540, h1550, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h1029, h1550, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1553 | h1553
                    · linarith only [h1029, h1388, h1539, h1540, h1553, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h1029, h1553, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h1519, h1548, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h0, h1539, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

set_option maxHeartbeats 3116000 in
set_option maxHeartbeats 3116000 in
theorem r1l7_21_14_H_I_L_0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_14_H_I_L_0_x0 m hb1 hb4 h0
  · exact r1l7_21_14_H_I_L_0_x1 m hb1 hb4 h0

end R2N4
