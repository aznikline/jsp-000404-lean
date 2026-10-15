import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x0_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8890 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9868 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9869 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9870 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9871 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9872 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 2 3 4 (by decide) (by decide) with h9873 | h9873
  · rcases m.htr 2 3 5 (by decide) (by decide) with h9874 | h9874
    · rcases m.htr 2 4 5 (by decide) (by decide) with h9875 | h9875
      · linarith only [h0, h6874, h8886, h8890, h9873, h9875, hc01, hc12, hlam, hphi]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h9877 | h9877
        · linarith only [h8889, h8890, h9877, hlam]
        · rcases h2bigk with h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c | h9879c
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [h0, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            rcases p9879_3 (m.d 0 2) (by simp) with h9882 | h9882
            · rcases p9879_3 (m.d 1 2) (by simp) with h9883 | h9883
              · rcases p9879_3 (m.d 2 3) (by simp) with h9884 | h9884
                · linarith only [h9884, hlam, p9879_0]
                · rcases p9879_3 (m.d 2 4) (by simp) with h9886 | h9886
                  · linarith only [h8887, h9886, hlam]
                  · rcases p9879_3 (m.d 2 5) (by simp) with h9888 | h9888
                    · linarith only [h8888, h9888, hlam]
                    · rcases h4bigk with h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c | h9890c
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h6874, hlam, p9890_1]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h8890, h9871, h9872, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9890_1]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h8890, h9871, h9872, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9890_1]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h8890, hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h6874, h9871, hc01, hc13, hlam, hphi, p9890_1]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        rcases p9890_3 (m.d 0 4) (by simp) with h9898 | h9898
                        · linarith only [h6874, h9898, hlam]
                        · linarith only [h8887, h9898, hlam]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        rcases p9890_3 (m.d 0 4) (by simp) with h9901 | h9901
                        · linarith only [h6874, h9901, hlam]
                        · linarith only [h8889, h9901, hlam]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h6874, h8890, h9868, h9871, hc01, hc12, hlam, hphi, p9890_1]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h8887, hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h9869, hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h0, h8887, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9890_1]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h9875, hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h8889, hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h9871, hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h9873, hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h9877, hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9890_1]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h9872, hlam, p9890_0]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h9868, h9871, h9872, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9890_1]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [h9868, h9871, h9872, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9890_1]
                      · have p9890_0 := h9890c.1
                        have p9890_1 := h9890c.2.1
                        have p9890_2 := h9890c.2.2.1
                        have p9890_3 := h9890c.2.2.2
                        linarith only [hlam, p9890_0]
              · linarith only [h9868, h9883, hlam]
            · linarith only [h9882, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            rcases p9879_3 (m.d 0 2) (by simp) with h9922 | h9922
            · rcases p9879_3 (m.d 1 2) (by simp) with h9923 | h9923
              · rcases p9879_3 (m.d 2 3) (by simp) with h9924 | h9924
                · linarith only [h8886, h9924, hlam]
                · linarith only [h9873, h9924, hlam]
              · linarith only [h9869, h9923, hlam]
            · linarith only [h9922, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            rcases p9879_3 (m.d 0 2) (by simp) with h9929 | h9929
            · rcases p9879_3 (m.d 1 2) (by simp) with h9930 | h9930
              · rcases p9879_3 (m.d 2 3) (by simp) with h9931 | h9931
                · linarith only [h8886, h9931, hlam]
                · linarith only [h9874, h9931, hlam]
              · linarith only [h9870, h9930, hlam]
            · linarith only [h9929, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [h8886, h9874, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p9879_1]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            rcases p9879_3 (m.d 0 2) (by simp) with h9938 | h9938
            · linarith only [h0, h9938, hlam]
            · linarith only [h8886, h9938, hlam]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            rcases p9879_3 (m.d 0 2) (by simp) with h9941 | h9941
            · linarith only [h0, h9941, hlam]
            · linarith only [h8887, h9941, hlam]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            rcases p9879_3 (m.d 0 2) (by simp) with h9944 | h9944
            · linarith only [h0, h9944, hlam]
            · linarith only [h8888, h9944, hlam]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [h8886, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [h9868, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            rcases p9879_3 (m.d 0 2) (by simp) with h9950 | h9950
            · rcases p9879_3 (m.d 1 2) (by simp) with h9951 | h9951
              · rcases p9879_3 (m.d 2 3) (by simp) with h9952 | h9952
                · rcases p9879_3 (m.d 2 4) (by simp) with h9953 | h9953
                  · linarith only [h9873, h9953, hlam]
                  · rcases p9879_3 (m.d 2 5) (by simp) with h9955 | h9955
                    · linarith only [h9874, h9955, hlam]
                    · linarith only [h9875, h9955, hlam]
                · linarith only [h9873, h9952, hlam]
              · linarith only [h9869, h9951, hlam]
            · linarith only [h8887, h9950, hlam]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            rcases p9879_3 (m.d 0 2) (by simp) with h9961 | h9961
            · rcases p9879_3 (m.d 1 2) (by simp) with h9962 | h9962
              · rcases p9879_3 (m.d 2 3) (by simp) with h9963 | h9963
                · rcases p9879_3 (m.d 2 4) (by simp) with h9964 | h9964
                  · linarith only [h9873, h9964, hlam]
                  · rcases p9879_3 (m.d 2 5) (by simp) with h9966 | h9966
                    · linarith only [h9874, h9966, hlam]
                    · rcases h4bigk with h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h6874, hlam, p9968_1]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h8890, h9868, h9871, h9872, h9873, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h8890, h9868, h9871, h9872, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h8890, hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h6874, h9868, h9871, hc01, hc12, hlam, hphi, p9968_1]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        rcases p9968_3 (m.d 0 4) (by simp) with h9976 | h9976
                        · linarith only [h6874, h9976, hlam]
                        · linarith only [h8887, h9976, hlam]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        rcases p9968_3 (m.d 0 4) (by simp) with h9979 | h9979
                        · linarith only [h6874, h9979, hlam]
                        · linarith only [h8889, h9979, hlam]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h6874, h8890, h9868, h9871, hc01, hc12, hlam, hphi, p9968_1]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h8887, hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h9869, hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h8887, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9968_1]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h9875, hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h8889, hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h9871, hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h9873, hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h9877, hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9968_1]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h9872, hlam, p9968_0]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h9868, h9871, h9872, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [h9868, h9871, h9872, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                      · have p9968_0 := h9968c.1
                        have p9968_1 := h9968c.2.1
                        have p9968_2 := h9968c.2.2.1
                        have p9968_3 := h9968c.2.2.2
                        linarith only [hlam, p9968_0]
                · linarith only [h9874, h9963, hlam]
              · linarith only [h9870, h9962, hlam]
            · linarith only [h8888, h9961, hlam]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [h8887, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [h9869, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [h9873, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [h9875, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [h8888, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [h9870, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [h9874, hlam, p9879_0]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            rcases p9879_3 (m.d 0 2) (by simp) with h10009 | h10009
            · rcases p9879_3 (m.d 1 2) (by simp) with h10010 | h10010
              · rcases p9879_3 (m.d 2 3) (by simp) with h10011 | h10011
                · rcases p9879_3 (m.d 2 4) (by simp) with h10012 | h10012
                  · linarith only [h10012, h9875, hlam]
                  · rcases p9879_3 (m.d 2 5) (by simp) with h10014 | h10014
                    · rcases h4bigk with h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c | h10015c
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h6874, hlam, p10015_1]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h8890, h9868, h9871, h9872, h9873, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10015_1]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h8890, h9868, h9871, h9872, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10015_1]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h8890, hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h6874, h9868, h9871, hc01, hc12, hlam, hphi, p10015_1]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        rcases p10015_3 (m.d 0 4) (by simp) with h10023 | h10023
                        · linarith only [h10023, h6874, hlam]
                        · linarith only [h10023, h8887, hlam]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        rcases p10015_3 (m.d 0 4) (by simp) with h10026 | h10026
                        · linarith only [h10026, h6874, hlam]
                        · linarith only [h10026, h8889, hlam]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h8888, h8890, h9868, h9871, h9873, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10015_1, p9879_1]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h8887, hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h9869, hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10015_1, p9879_1]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h9875, hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h8889, hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h9871, hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h9873, hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h9877, hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h6874, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10015_1]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h9872, hlam, p10015_0]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h9868, h9871, h9872, h9873, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10015_1]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [h9868, h9871, h9872, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10015_1]
                      · have p10015_0 := h10015c.1
                        have p10015_1 := h10015c.2.1
                        have p10015_2 := h10015c.2.2.1
                        have p10015_3 := h10015c.2.2.2
                        linarith only [hlam, p10015_0]
                    · linarith only [h10014, h9875, hlam]
                · linarith only [h10011, h9873, hlam]
              · linarith only [h10010, h9869, hlam]
            · linarith only [h10009, h8887, hlam]
          · have p9879_0 := h9879c.1
            have p9879_1 := h9879c.2.1
            have p9879_2 := h9879c.2.2.1
            have p9879_3 := h9879c.2.2.2
            linarith only [hlam, p9879_0]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h10050 | h10050
      · linarith only [h10050, h8887, h8890, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h10052 | h10052
        · linarith only [h10052, h6874, h8890, h9873, hc01, hc23, hlam, hphi, ht12]
        · rcases h2bigk with h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c | h10054c
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h0, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            rcases p10054_3 (m.d 0 2) (by simp) with h10057 | h10057
            · rcases p10054_3 (m.d 1 2) (by simp) with h10058 | h10058
              · rcases p10054_3 (m.d 2 3) (by simp) with h10059 | h10059
                · linarith only [h10059, hlam, p10054_0]
                · rcases p10054_3 (m.d 2 4) (by simp) with h10061 | h10061
                  · linarith only [h10061, h8887, hlam]
                  · rcases p10054_3 (m.d 2 5) (by simp) with h10063 | h10063
                    · linarith only [h10063, h8888, hlam]
                    · linarith only [h10063, h9874, hlam]
              · linarith only [h10058, h9868, hlam]
            · linarith only [h10057, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            rcases p10054_3 (m.d 0 2) (by simp) with h10068 | h10068
            · rcases p10054_3 (m.d 1 2) (by simp) with h10069 | h10069
              · rcases p10054_3 (m.d 2 3) (by simp) with h10070 | h10070
                · linarith only [h10070, h8886, hlam]
                · linarith only [h10070, h9873, hlam]
              · linarith only [h10069, h9869, hlam]
            · linarith only [h10068, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            rcases p10054_3 (m.d 0 2) (by simp) with h10075 | h10075
            · rcases p10054_3 (m.d 1 2) (by simp) with h10076 | h10076
              · rcases p10054_3 (m.d 2 3) (by simp) with h10077 | h10077
                · linarith only [h10077, h8886, hlam]
                · rcases p10054_3 (m.d 2 4) (by simp) with h10079 | h10079
                  · linarith only [h10079, h8887, hlam]
                  · rcases p10054_3 (m.d 2 5) (by simp) with h10081 | h10081
                    · linarith only [h10081, hlam, p10054_0]
                    · rcases h4bigk with h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c | h10083c
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h6874, hlam, p10083_1]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h8890, h9868, h9871, h9872, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10083_1]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h8890, h9868, h9871, h9872, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10083_1]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h8890, hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h6874, h9868, h9871, hc01, hc12, hlam, hphi, p10083_1]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        rcases p10083_3 (m.d 0 4) (by simp) with h10091 | h10091
                        · linarith only [h10091, h6874, hlam]
                        · linarith only [h10091, h8887, hlam]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        rcases p10083_3 (m.d 0 4) (by simp) with h10094 | h10094
                        · linarith only [h10094, h6874, hlam]
                        · linarith only [h10094, h8889, hlam]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h10052, h9868, h9871, h9874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10083_1]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h8887, hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h9869, hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h0, h8887, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10083_1]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h10050, hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h8889, hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h9871, hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h9873, hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h10052, hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [hc04, hc45, hlam, hphi, p10083_1]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h9872, hlam, p10083_0]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h9868, h9871, h9872, h9873, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10083_1]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [h9868, h9871, h9872, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10083_1]
                      · have p10083_0 := h10083c.1
                        have p10083_1 := h10083c.2.1
                        have p10083_2 := h10083c.2.2.1
                        have p10083_3 := h10083c.2.2.2
                        linarith only [hlam, p10083_0]
              · linarith only [h10076, h9870, hlam]
            · linarith only [h10075, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h8886, h9873, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10054_1]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            rcases p10054_3 (m.d 0 2) (by simp) with h10117 | h10117
            · linarith only [h0, h10117, hlam]
            · linarith only [h10117, h8886, hlam]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            rcases p10054_3 (m.d 0 2) (by simp) with h10120 | h10120
            · linarith only [h0, h10120, hlam]
            · linarith only [h10120, h8887, hlam]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            rcases p10054_3 (m.d 0 2) (by simp) with h10123 | h10123
            · linarith only [h0, h10123, hlam]
            · linarith only [h10123, h8888, hlam]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h8886, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h9868, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h10052, h9868, h9871, h9872, h9873, h9874, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10054_1]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h9874, hlam, p10054_1]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h8887, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h9869, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h9873, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h10050, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h8888, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h9870, hlam, p10054_0]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [h8888, h8890, h9868, h9871, h9872, h9873, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10054_1]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            rcases p10054_3 (m.d 0 2) (by simp) with h10139 | h10139
            · rcases p10054_3 (m.d 1 2) (by simp) with h10140 | h10140
              · rcases p10054_3 (m.d 2 3) (by simp) with h10141 | h10141
                · linarith only [h10141, h9874, hlam]
                · linarith only [h10141, h9873, hlam]
              · linarith only [h10140, h9869, hlam]
            · linarith only [h10139, h8887, hlam]
          · have p10054_0 := h10054c.1
            have p10054_1 := h10054c.2.1
            have p10054_2 := h10054c.2.2.1
            have p10054_3 := h10054c.2.2.2
            linarith only [hlam, p10054_0]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h10147 | h10147
    · linarith only [h10147, h8889, h8890, h9868, h9871, h9872, h9873, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h10149 | h10149
      · linarith only [h0, h10149, h8887, h8889, h8890, h9873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h10151 | h10151
        · linarith only [h10151, h8889, h8890, hlam]
        · rcases h2bigk with h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c | h10153c
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h0, hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            rcases p10153_3 (m.d 0 2) (by simp) with h10156 | h10156
            · rcases p10153_3 (m.d 1 2) (by simp) with h10157 | h10157
              · rcases p10153_3 (m.d 2 3) (by simp) with h10158 | h10158
                · linarith only [h10158, hlam, p10153_0]
                · rcases p10153_3 (m.d 2 4) (by simp) with h10160 | h10160
                  · linarith only [h10160, h8887, hlam]
                  · linarith only [h10160, h9873, hlam]
              · linarith only [h10157, h9868, hlam]
            · linarith only [h10156, hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            rcases p10153_3 (m.d 0 2) (by simp) with h10165 | h10165
            · rcases p10153_3 (m.d 1 2) (by simp) with h10166 | h10166
              · rcases p10153_3 (m.d 2 3) (by simp) with h10167 | h10167
                · linarith only [h10167, h8886, hlam]
                · rcases p10153_3 (m.d 2 4) (by simp) with h10169 | h10169
                  · linarith only [h10169, hlam, p10153_0]
                  · rcases p10153_3 (m.d 2 5) (by simp) with h10171 | h10171
                    · linarith only [h10171, h8888, hlam]
                    · linarith only [h10149, h10171, hlam]
              · linarith only [h10166, h9869, hlam]
            · linarith only [h10165, hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            rcases p10153_3 (m.d 0 2) (by simp) with h10176 | h10176
            · rcases p10153_3 (m.d 1 2) (by simp) with h10177 | h10177
              · rcases p10153_3 (m.d 2 3) (by simp) with h10178 | h10178
                · linarith only [h10178, h8886, hlam]
                · rcases p10153_3 (m.d 2 4) (by simp) with h10180 | h10180
                  · linarith only [h10180, h8887, hlam]
                  · rcases p10153_3 (m.d 2 5) (by simp) with h10182 | h10182
                    · linarith only [h10182, hlam, p10153_0]
                    · rcases h4bigk with h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c | h10184c
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h6874, hlam, p10184_1]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h8890, hc24, hc45, hlam, hphi, p10184_1]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h8890, h9873, hc23, hc45, hlam, hphi, ht34, p10184_1]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h8890, hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h6874, h9868, h9871, hc01, hc12, hlam, hphi, p10184_1]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        rcases p10184_3 (m.d 0 4) (by simp) with h10192 | h10192
                        · linarith only [h10192, h6874, hlam]
                        · linarith only [h10192, h8887, hlam]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h9868, h9871, h9873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10184_1]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h8889, h8890, h9868, h9871, h9873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10184_1]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h8887, hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h9869, hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h9873, hlam, p10184_1]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h10149, hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h8889, hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h9871, hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h8889, h9873, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10184_1]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h10151, hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [hc04, hc45, hlam, hphi, p10184_1]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h9872, hlam, p10184_0]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h9868, h9871, h9872, h9873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10184_1]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [h9868, h9871, h9872, h9873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10184_1]
                      · have p10184_0 := h10184c.1
                        have p10184_1 := h10184c.2.1
                        have p10184_2 := h10184c.2.2.1
                        have p10184_3 := h10184c.2.2.2
                        linarith only [hlam, p10184_0]
              · linarith only [h10177, h9870, hlam]
            · linarith only [h10176, hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h8886, h8889, h9873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10153_1]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h8889, h8890, h9868, h9871, h9872, h9873, hlam, p10153_2]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            rcases p10153_3 (m.d 0 2) (by simp) with h10217 | h10217
            · linarith only [h0, h10217, hlam]
            · linarith only [h10217, h8887, hlam]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            rcases p10153_3 (m.d 0 2) (by simp) with h10220 | h10220
            · linarith only [h0, h10220, hlam]
            · linarith only [h10220, h8888, hlam]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h8886, hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h9868, hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h9873, hlam, p10153_1]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h10147, hlam, p10153_1]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h8887, hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h9869, hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h8887, h8890, h9868, h9871, h9872, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10153_1]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h10149, hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h8888, hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [h9870, hlam, p10153_0]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            rcases p10153_3 (m.d 0 2) (by simp) with h10235 | h10235
            · rcases p10153_3 (m.d 1 2) (by simp) with h10236 | h10236
              · rcases p10153_3 (m.d 2 3) (by simp) with h10237 | h10237
                · linarith only [h10147, h10237, hlam]
                · rcases p10153_3 (m.d 2 4) (by simp) with h10239 | h10239
                  · linarith only [h10149, h10239, hlam]
                  · linarith only [h10239, h9873, hlam]
              · linarith only [h10236, h9868, hlam]
            · linarith only [h10235, h8886, hlam]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            rcases p10153_3 (m.d 0 2) (by simp) with h10244 | h10244
            · rcases p10153_3 (m.d 1 2) (by simp) with h10245 | h10245
              · rcases p10153_3 (m.d 2 3) (by simp) with h10246 | h10246
                · linarith only [h10147, h10246, hlam]
                · rcases p10153_3 (m.d 2 4) (by simp) with h10248 | h10248
                  · linarith only [h10149, h10248, hlam]
                  · rcases p10153_3 (m.d 2 5) (by simp) with h10250 | h10250
                    · rcases h4bigk with h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c | h10251c
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h6874, hlam, p10251_1]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h8890, h9868, h9871, h9872, h9873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10251_1]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h8890, h9868, h9871, h9872, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10251_1]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h8890, hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h6874, h9868, h9871, hc01, hc12, hlam, hphi, p10251_1]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        rcases p10251_3 (m.d 0 4) (by simp) with h10259 | h10259
                        · linarith only [h10259, h6874, hlam]
                        · linarith only [h10259, h8887, hlam]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h9868, h9871, h9873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10251_1]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h8888, h8890, h9868, h9871, h9873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10153_1, p10251_1]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h8887, hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h9869, hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h9873, hlam, p10251_1]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h10149, hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h8889, hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h9871, hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h8889, h9873, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10251_1]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h10151, hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [hc04, hc45, hlam, hphi, p10251_1]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h9872, hlam, p10251_0]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h9868, h9871, h9872, h9873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10251_1]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [h9868, h9871, h9872, h9873, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10251_1]
                      · have p10251_0 := h10251c.1
                        have p10251_1 := h10251c.2.1
                        have p10251_2 := h10251c.2.2.1
                        have p10251_3 := h10251c.2.2.2
                        linarith only [hlam, p10251_0]
                    · linarith only [h10149, h10250, hlam]
              · linarith only [h10245, h9869, hlam]
            · linarith only [h10244, h8887, hlam]
          · have p10153_0 := h10153c.1
            have p10153_1 := h10153c.2.1
            have p10153_2 := h10153c.2.2.1
            have p10153_3 := h10153c.2.2.2
            linarith only [hlam, p10153_0]

end R2N4
