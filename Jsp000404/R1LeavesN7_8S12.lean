import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9896 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h9897 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h9898 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  rcases m.htr 2 3 5 (by decide) (by decide) with h9899 | h9899
  · rcases m.htr 2 4 5 (by decide) (by decide) with h9900 | h9900
    · rcases m.htr 3 4 5 (by decide) (by decide) with h9901 | h9901
      · linarith only [h9886, h9898, h9901, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
      · rcases h0bigk with h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c | h9903c
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [hlam, p9903_0]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h0, hlam, p9903_1]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h7600, hlam, p9903_0]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h8836, hlam, p9903_1]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h9666, hlam, p9903_1]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          rcases p9903_3 (m.d 0 1) (by simp) with h9909 | h9909
          · linarith only [h0, h9909, hlam]
          · rcases p9903_3 (m.d 0 2) (by simp) with h9911 | h9911
            · rcases p9903_3 (m.d 0 3) (by simp) with h9912 | h9912
              · linarith only [h9886, h9912, hlam]
              · linarith only [h7600, h9912, hlam]
            · linarith only [h0, h9911, hlam]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [hlam, p9903_0]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h0, h9887, h9889, h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9903_1]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h0, h9887, h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9903_1]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          rcases p9903_3 (m.d 0 1) (by simp) with h9919 | h9919
          · linarith only [h0, h9919, hlam]
          · rcases p9903_3 (m.d 0 2) (by simp) with h9921 | h9921
            · rcases p9903_3 (m.d 0 3) (by simp) with h9922 | h9922
              · linarith only [h9886, h9922, hlam]
              · linarith only [h9890, h9922, hlam]
            · linarith only [h9888, h9921, hlam]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          rcases p9903_3 (m.d 0 1) (by simp) with h9926 | h9926
          · linarith only [h7600, h9926, hlam]
          · rcases p9903_3 (m.d 0 2) (by simp) with h9928 | h9928
            · rcases p9903_3 (m.d 0 3) (by simp) with h9929 | h9929
              · rcases p9903_3 (m.d 0 4) (by simp) with h9930 | h9930
                · linarith only [h9889, h9930, hlam]
                · linarith only [h8836, h9930, hlam]
              · linarith only [h7600, h9929, hlam]
            · linarith only [h0, h9928, hlam]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h9886, hlam, p9903_1]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [hlam, p9903_0]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h9887, h9900, h9901, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9903_1]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          rcases p9903_3 (m.d 0 1) (by simp) with h9938 | h9938
          · linarith only [h7600, h9938, hlam]
          · rcases p9903_3 (m.d 0 2) (by simp) with h9940 | h9940
            · rcases p9903_3 (m.d 0 3) (by simp) with h9941 | h9941
              · rcases p9903_3 (m.d 0 4) (by simp) with h9942 | h9942
                · linarith only [h9889, h9942, hlam]
                · linarith only [h9891, h9942, hlam]
              · linarith only [h9890, h9941, hlam]
            · linarith only [h9888, h9940, hlam]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          rcases p9903_3 (m.d 0 1) (by simp) with h9947 | h9947
          · linarith only [h8836, h9947, hlam]
          · rcases p9903_3 (m.d 0 2) (by simp) with h9949 | h9949
            · rcases p9903_3 (m.d 0 3) (by simp) with h9950 | h9950
              · rcases p9903_3 (m.d 0 4) (by simp) with h9951 | h9951
                · rcases p9903_3 (m.d 0 5) (by simp) with h9952 | h9952
                  · linarith only [h9891, h9952, hlam]
                  · linarith only [h9666, h9952, hlam]
                · linarith only [h8836, h9951, hlam]
              · linarith only [h7600, h9950, hlam]
            · linarith only [h0, h9949, hlam]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h9887, hlam, p9903_0]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h9889, hlam, p9903_0]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [hlam, p9903_0]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          rcases p9903_3 (m.d 0 1) (by simp) with h9961 | h9961
          · linarith only [h8836, h9961, hlam]
          · rcases p9903_3 (m.d 0 2) (by simp) with h9963 | h9963
            · rcases p9903_3 (m.d 0 3) (by simp) with h9964 | h9964
              · rcases p9903_3 (m.d 0 4) (by simp) with h9965 | h9965
                · rcases p9903_3 (m.d 0 5) (by simp) with h9966 | h9966
                  · linarith only [h9891, h9966, hlam]
                  · rcases h2bigk with h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c | h9968c
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h0, hlam, p9968_1]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h0, h9898, h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h0, h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      rcases p9968_3 (m.d 0 2) (by simp) with h9973 | h9973
                      · rcases p9968_3 (m.d 1 2) (by simp) with h9974 | h9974
                        · rcases p9968_3 (m.d 2 3) (by simp) with h9975 | h9975
                          · linarith only [h9886, h9975, hlam]
                          · linarith only [h9899, h9975, hlam]
                        · linarith only [h9894, h9974, hlam]
                      · linarith only [h9973, hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9886, h9898, h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9898, h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9968_1]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      rcases p9968_3 (m.d 0 2) (by simp) with h9984 | h9984
                      · linarith only [h0, h9984, hlam]
                      · linarith only [h9888, h9984, hlam]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9886, hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9892, hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9900, h9901, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9968_1]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9886, hc02, hlam, hphi, ht0b, ht5b, p9968_1, u5ehi2]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9887, hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9893, hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9898, hlam, p9968_1]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h0, h9887, h9899, hc12, hlam, hphi, ht01, ht0b, ht5b, p9968_1, u5ehi3]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9888, hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9894, hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9899, hlam, p9968_1]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [h9900, hlam, p9968_0]
                    · have p9968_0 := h9968c.1
                      have p9968_1 := h9968c.2.1
                      have p9968_2 := h9968c.2.2.1
                      have p9968_3 := h9968c.2.2.2
                      linarith only [hlam, p9968_0]
                · linarith only [h9891, h9965, hlam]
              · linarith only [h9890, h9964, hlam]
            · linarith only [h9888, h9963, hlam]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          rcases p9903_3 (m.d 0 1) (by simp) with h10005 | h10005
          · linarith only [h10005, h9666, hlam]
          · rcases p9903_3 (m.d 0 2) (by simp) with h10007 | h10007
            · rcases p9903_3 (m.d 0 3) (by simp) with h10008 | h10008
              · rcases p9903_3 (m.d 0 4) (by simp) with h10009 | h10009
                · rcases p9903_3 (m.d 0 5) (by simp) with h10010 | h10010
                  · rcases h2bigk with h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c | h10011c
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h0, hlam, p10011_1]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h0, h9899, hc12, hlam, hphi, ht01, ht0b, ht5b, p10011_1, u5ehi3]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h0, h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10011_1]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      rcases p10011_3 (m.d 0 2) (by simp) with h10016 | h10016
                      · rcases p10011_3 (m.d 1 2) (by simp) with h10017 | h10017
                        · rcases p10011_3 (m.d 2 3) (by simp) with h10018 | h10018
                          · linarith only [h10018, h9886, hlam]
                          · linarith only [h10018, h9899, hlam]
                        · linarith only [h10017, h9894, hlam]
                      · linarith only [h10016, hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9886, h9898, h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10011_1]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9898, h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10011_1]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10011_1]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      rcases p10011_3 (m.d 0 2) (by simp) with h10027 | h10027
                      · linarith only [h0, h10027, hlam]
                      · linarith only [h10027, h9888, hlam]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9886, hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9892, hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9900, h9901, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10011_1]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h0, h9886, h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10011_1]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9887, hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9893, hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9898, hlam, p10011_1]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h0, h9887, h9900, h9901, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10011_1]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9888, hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9894, hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9899, hlam, p10011_1]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [h9900, hlam, p10011_0]
                    · have p10011_0 := h10011c.1
                      have p10011_1 := h10011c.2.1
                      have p10011_2 := h10011c.2.2.1
                      have p10011_3 := h10011c.2.2.2
                      linarith only [hlam, p10011_0]
                  · linarith only [h10010, h9666, hlam]
                · linarith only [h10009, h8836, hlam]
              · linarith only [h10008, h7600, hlam]
            · linarith only [h0, h10007, hlam]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h9888, hlam, p9903_1]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h9890, hlam, p9903_0]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [h9891, hlam, p9903_1]
        · have p9903_0 := h9903c.1
          have p9903_1 := h9903c.2.1
          have p9903_2 := h9903c.2.2.1
          have p9903_3 := h9903c.2.2.2
          linarith only [hlam, p9903_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h10053 | h10053
      · linarith only [h0, h10053, h9886, h9898, h9900, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h0bigk with h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c | h10055c
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [hlam, p10055_0]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h0, hlam, p10055_1]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h7600, hlam, p10055_0]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h8836, hlam, p10055_1]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h9666, hlam, p10055_1]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          rcases p10055_3 (m.d 0 1) (by simp) with h10061 | h10061
          · linarith only [h0, h10061, hlam]
          · rcases p10055_3 (m.d 0 2) (by simp) with h10063 | h10063
            · rcases p10055_3 (m.d 0 3) (by simp) with h10064 | h10064
              · linarith only [h10064, h9886, hlam]
              · linarith only [h10064, h7600, hlam]
            · linarith only [h0, h10063, hlam]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [hlam, p10055_0]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h0, h9889, h9891, h9898, h9900, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10055_1]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h0, h9891, h9898, h9900, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10055_1]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          rcases p10055_3 (m.d 0 1) (by simp) with h10071 | h10071
          · linarith only [h0, h10071, hlam]
          · rcases p10055_3 (m.d 0 2) (by simp) with h10073 | h10073
            · rcases p10055_3 (m.d 0 3) (by simp) with h10074 | h10074
              · linarith only [h10074, h9886, hlam]
              · linarith only [h10074, h9890, hlam]
            · linarith only [h10073, h9888, hlam]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          rcases p10055_3 (m.d 0 1) (by simp) with h10078 | h10078
          · linarith only [h10078, h7600, hlam]
          · rcases p10055_3 (m.d 0 2) (by simp) with h10080 | h10080
            · rcases p10055_3 (m.d 0 3) (by simp) with h10081 | h10081
              · rcases p10055_3 (m.d 0 4) (by simp) with h10082 | h10082
                · linarith only [h10082, h9889, hlam]
                · linarith only [h10082, h8836, hlam]
              · linarith only [h10081, h7600, hlam]
            · linarith only [h0, h10080, hlam]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h9886, hlam, p10055_1]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [hlam, p10055_0]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h9891, h9898, h9900, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10055_1]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          rcases p10055_3 (m.d 0 1) (by simp) with h10090 | h10090
          · linarith only [h10090, h7600, hlam]
          · rcases p10055_3 (m.d 0 2) (by simp) with h10092 | h10092
            · rcases p10055_3 (m.d 0 3) (by simp) with h10093 | h10093
              · rcases p10055_3 (m.d 0 4) (by simp) with h10094 | h10094
                · linarith only [h10094, h9889, hlam]
                · linarith only [h10094, h9891, hlam]
              · linarith only [h10093, h9890, hlam]
            · linarith only [h10092, h9888, hlam]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          rcases p10055_3 (m.d 0 1) (by simp) with h10099 | h10099
          · linarith only [h10099, h8836, hlam]
          · rcases p10055_3 (m.d 0 2) (by simp) with h10101 | h10101
            · rcases p10055_3 (m.d 0 3) (by simp) with h10102 | h10102
              · rcases p10055_3 (m.d 0 4) (by simp) with h10103 | h10103
                · rcases p10055_3 (m.d 0 5) (by simp) with h10104 | h10104
                  · linarith only [h10104, h9891, hlam]
                  · linarith only [h10104, h9666, hlam]
                · linarith only [h10103, h8836, hlam]
              · linarith only [h10102, h7600, hlam]
            · linarith only [h0, h10101, hlam]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h9887, hlam, p10055_0]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h9889, hlam, p10055_0]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [hlam, p10055_0]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          rcases p10055_3 (m.d 0 1) (by simp) with h10113 | h10113
          · linarith only [h10113, h8836, hlam]
          · rcases p10055_3 (m.d 0 2) (by simp) with h10115 | h10115
            · rcases p10055_3 (m.d 0 3) (by simp) with h10116 | h10116
              · rcases p10055_3 (m.d 0 4) (by simp) with h10117 | h10117
                · rcases p10055_3 (m.d 0 5) (by simp) with h10118 | h10118
                  · linarith only [h10118, h9891, hlam]
                  · rcases h2bigk with h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c | h10120c
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [hlam, p10120_0]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h0, hlam, p10120_1]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h0, h9899, hc12, hlam, hphi, ht01, ht0b, ht5b, p10120_1, u5ehi3]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9887, h9891, h9900, hlam, p10055_1, p10120_2]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      rcases p10120_3 (m.d 0 2) (by simp) with h10125 | h10125
                      · rcases p10120_3 (m.d 1 2) (by simp) with h10126 | h10126
                        · rcases p10120_3 (m.d 2 3) (by simp) with h10127 | h10127
                          · linarith only [h10127, h9886, hlam]
                          · linarith only [h10127, h9899, hlam]
                        · linarith only [h10126, h9894, hlam]
                      · linarith only [h10125, hlam, p10120_0]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9886, h9889, h9891, h9898, h9900, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10055_1, p10120_1]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [hlam, p10120_0]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9899, hc12, hlam, hphi, ht01, ht0b, ht5b, p10120_1, u5ehi3]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h0, h9886, h9889, h9891, h9900, hlam, p10055_1, p10120_2]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      rcases p10120_3 (m.d 0 2) (by simp) with h10136 | h10136
                      · linarith only [h0, h10136, hlam]
                      · linarith only [h10136, h9888, hlam]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9886, hlam, p10120_0]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9892, hlam, p10120_0]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [hlam, p10120_0]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      rcases p10120_3 (m.d 0 2) (by simp) with h10142 | h10142
                      · rcases p10120_3 (m.d 1 2) (by simp) with h10143 | h10143
                        · rcases p10120_3 (m.d 2 3) (by simp) with h10144 | h10144
                          · rcases p10120_3 (m.d 2 4) (by simp) with h10145 | h10145
                            · linarith only [h10145, h9898, hlam]
                            · rcases p10120_3 (m.d 2 5) (by simp) with h10147 | h10147
                              · linarith only [h10147, h9899, hlam]
                              · linarith only [h10147, h9900, hlam]
                          · linarith only [h10144, h9898, hlam]
                        · linarith only [h10143, h9893, hlam]
                      · linarith only [h10142, h9887, hlam]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9886, h9899, hc02, hlam, hphi, ht0b, ht5b, p10120_1, u5ehi3]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9887, hlam, p10120_0]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9893, hlam, p10120_0]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9898, hlam, p10120_1]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [hlam, p10120_0]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9900, hlam, p10120_1]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9888, hlam, p10120_0]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9894, hlam, p10120_0]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9899, hlam, p10120_1]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [h9888, h9889, h9898, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10055_1, p10120_1]
                    · have p10120_0 := h10120c.1
                      have p10120_1 := h10120c.2.1
                      have p10120_2 := h10120c.2.2.1
                      have p10120_3 := h10120c.2.2.2
                      linarith only [hlam, p10120_0]
                · linarith only [h10117, h9891, hlam]
              · linarith only [h10116, h9890, hlam]
            · linarith only [h10115, h9888, hlam]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          rcases p10055_3 (m.d 0 1) (by simp) with h10167 | h10167
          · linarith only [h10167, h9666, hlam]
          · rcases p10055_3 (m.d 0 2) (by simp) with h10169 | h10169
            · rcases p10055_3 (m.d 0 3) (by simp) with h10170 | h10170
              · rcases p10055_3 (m.d 0 4) (by simp) with h10171 | h10171
                · rcases p10055_3 (m.d 0 5) (by simp) with h10172 | h10172
                  · rcases h2bigk with h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h0, hlam, p10173_1]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h0, h9899, hc12, hlam, hphi, ht01, ht0b, ht5b, p10173_1, u5ehi3]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      rcases p10173_3 (m.d 0 2) (by simp) with h10177 | h10177
                      · rcases p10173_3 (m.d 1 2) (by simp) with h10178 | h10178
                        · rcases p10173_3 (m.d 2 3) (by simp) with h10179 | h10179
                          · linarith only [h10179, h9886, hlam]
                          · linarith only [h10179, h9898, hlam]
                        · linarith only [h10178, h9893, hlam]
                      · linarith only [h10177, hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      rcases p10173_3 (m.d 0 2) (by simp) with h10184 | h10184
                      · rcases p10173_3 (m.d 1 2) (by simp) with h10185 | h10185
                        · rcases p10173_3 (m.d 2 3) (by simp) with h10186 | h10186
                          · linarith only [h10186, h9886, hlam]
                          · linarith only [h10186, h9899, hlam]
                        · linarith only [h10185, h9894, hlam]
                      · linarith only [h10184, hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9886, h9899, hc12, hlam, hphi, ht01, ht0b, ht5b, p10173_1, u5ehi3]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9899, hc12, hlam, hphi, ht01, ht0b, ht5b, p10173_1, u5ehi3]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      rcases p10173_3 (m.d 0 2) (by simp) with h10194 | h10194
                      · linarith only [h0, h10194, hlam]
                      · linarith only [h10194, h9887, hlam]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      rcases p10173_3 (m.d 0 2) (by simp) with h10197 | h10197
                      · linarith only [h0, h10197, hlam]
                      · linarith only [h10197, h9888, hlam]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9886, hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9892, hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      rcases p10173_3 (m.d 0 2) (by simp) with h10203 | h10203
                      · rcases p10173_3 (m.d 1 2) (by simp) with h10204 | h10204
                        · rcases p10173_3 (m.d 2 3) (by simp) with h10205 | h10205
                          · rcases p10173_3 (m.d 2 4) (by simp) with h10206 | h10206
                            · linarith only [h10206, h9898, hlam]
                            · rcases p10173_3 (m.d 2 5) (by simp) with h10208 | h10208
                              · linarith only [h10208, h9899, hlam]
                              · linarith only [h10208, h9900, hlam]
                          · linarith only [h10205, h9898, hlam]
                        · linarith only [h10204, h9893, hlam]
                      · linarith only [h10203, h9887, hlam]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9886, hc02, hlam, hphi, ht0b, ht5b, p10173_1, u5ehi2]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9887, hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9893, hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9898, hlam, p10173_1]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9900, hlam, p10173_1]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9888, hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9894, hlam, p10173_0]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [h9899, hlam, p10173_1]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      rcases p10173_3 (m.d 0 2) (by simp) with h10223 | h10223
                      · rcases p10173_3 (m.d 1 2) (by simp) with h10224 | h10224
                        · rcases p10173_3 (m.d 2 3) (by simp) with h10225 | h10225
                          · rcases p10173_3 (m.d 2 4) (by simp) with h10226 | h10226
                            · linarith only [h10226, h9900, hlam]
                            · rcases p10173_3 (m.d 2 5) (by simp) with h10228 | h10228
                              · rcases h3bigk with h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c | h10229c
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h7600, hlam, p10229_1]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h0, h9886, h9899, hc12, hlam, hphi, ht01, ht0b, ht5b, p10229_1, u5ehi3]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9889, h9891, h9898, h9900, hlam, p10173_1, p10229_2]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  rcases p10229_3 (m.d 0 3) (by simp) with h10234 | h10234
                                  · rcases p10229_3 (m.d 1 3) (by simp) with h10235 | h10235
                                    · rcases p10229_3 (m.d 2 3) (by simp) with h10236 | h10236
                                      · linarith only [h10236, h9886, hlam]
                                      · linarith only [h10236, h9899, hlam]
                                    · linarith only [h10235, h9896, hlam]
                                  · linarith only [h10234, hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9889, h9891, h9892, h9898, h9900, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10173_1, p10229_1]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9892, h9898, h9899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10173_1, p10229_1]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h7600, h9889, h9891, h9898, h9900, hlam, p10173_1, p10229_2]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  rcases p10229_3 (m.d 0 3) (by simp) with h10245 | h10245
                                  · linarith only [h10245, h7600, hlam]
                                  · linarith only [h10245, h9890, hlam]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9886, hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9892, hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  rcases p10229_3 (m.d 0 3) (by simp) with h10251 | h10251
                                  · rcases p10229_3 (m.d 1 3) (by simp) with h10252 | h10252
                                    · rcases p10229_3 (m.d 2 3) (by simp) with h10253 | h10253
                                      · rcases p10229_3 (m.d 3 4) (by simp) with h10254 | h10254
                                        · linarith only [h10254, hlam, p10229_0]
                                        · rcases p10229_3 (m.d 3 5) (by simp) with h10256 | h10256
                                          · linarith only [h10256, h9899, hlam]
                                          · linarith only [h10053, h10256, hlam]
                                      · linarith only [h10253, hlam, p10229_0]
                                    · linarith only [h10252, h9895, hlam]
                                  · linarith only [h10251, h9889, hlam]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9886, hc02, hlam, hphi, ht0b, ht5b, p10229_1, u5ehi3]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9889, hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9895, hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9898, hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h10053, hlam, p10229_1]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9890, hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9896, hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h9899, hlam, p10229_0]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [h0, h9886, h9899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10229_1]
                                · have p10229_0 := h10229c.1
                                  have p10229_1 := h10229c.2.1
                                  have p10229_2 := h10229c.2.2.1
                                  have p10229_3 := h10229c.2.2.2
                                  linarith only [hlam, p10229_0]
                              · linarith only [h10228, h9900, hlam]
                          · linarith only [h10225, h9898, hlam]
                        · linarith only [h10224, h9893, hlam]
                      · linarith only [h10223, h9887, hlam]
                    · have p10173_0 := h10173c.1
                      have p10173_1 := h10173c.2.1
                      have p10173_2 := h10173c.2.2.1
                      have p10173_3 := h10173c.2.2.2
                      linarith only [hlam, p10173_0]
                  · linarith only [h10172, h9666, hlam]
                · linarith only [h10171, h8836, hlam]
              · linarith only [h10170, h7600, hlam]
            · linarith only [h0, h10169, hlam]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h9888, hlam, p10055_1]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h9890, hlam, p10055_0]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [h9891, hlam, p10055_1]
        · have p10055_0 := h10055c.1
          have p10055_1 := h10055c.2.1
          have p10055_2 := h10055c.2.2.1
          have p10055_3 := h10055c.2.2.2
          linarith only [hlam, p10055_0]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h10286 | h10286
    · linarith only [h10286, h9890, h9898, h9899, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h10288 | h10288
      · linarith only [h0, h10286, h10288, h9886, h9890, h9898, h9899, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · rcases h0bigk with h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c | h10290c
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [hlam, p10290_0]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h0, hlam, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h7600, hlam, p10290_0]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h8836, hlam, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h9666, hlam, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          rcases p10290_3 (m.d 0 1) (by simp) with h10296 | h10296
          · linarith only [h0, h10296, hlam]
          · rcases p10290_3 (m.d 0 2) (by simp) with h10298 | h10298
            · rcases p10290_3 (m.d 0 3) (by simp) with h10299 | h10299
              · linarith only [h10299, h9886, hlam]
              · linarith only [h10299, h7600, hlam]
            · linarith only [h0, h10298, hlam]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [hlam, p10290_0]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h0, h10288, h9889, h9891, h9899, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h0, h10288, h9891, h9898, h9899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h0, h9890, h9898, h9899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          rcases p10290_3 (m.d 0 1) (by simp) with h10307 | h10307
          · linarith only [h10307, h7600, hlam]
          · rcases p10290_3 (m.d 0 2) (by simp) with h10309 | h10309
            · rcases p10290_3 (m.d 0 3) (by simp) with h10310 | h10310
              · rcases p10290_3 (m.d 0 4) (by simp) with h10311 | h10311
                · linarith only [h10311, h9889, hlam]
                · linarith only [h10311, h8836, hlam]
              · linarith only [h10310, h7600, hlam]
            · linarith only [h0, h10309, hlam]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h9886, hlam, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [hlam, p10290_0]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h10288, h9891, h9898, h9899, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h10288, h7600, h9891, h9892, h9898, h9899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          rcases p10290_3 (m.d 0 1) (by simp) with h10320 | h10320
          · linarith only [h10320, h8836, hlam]
          · rcases p10290_3 (m.d 0 2) (by simp) with h10322 | h10322
            · rcases p10290_3 (m.d 0 3) (by simp) with h10323 | h10323
              · rcases p10290_3 (m.d 0 4) (by simp) with h10324 | h10324
                · rcases p10290_3 (m.d 0 5) (by simp) with h10325 | h10325
                  · linarith only [h10325, h9891, hlam]
                  · linarith only [h10325, h9666, hlam]
                · linarith only [h10324, h8836, hlam]
              · linarith only [h10323, h7600, hlam]
            · linarith only [h0, h10322, hlam]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h9887, hlam, p10290_0]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h9889, hlam, p10290_0]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [hlam, p10290_0]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h10288, h9891, h9898, h9899, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          rcases p10290_3 (m.d 0 1) (by simp) with h10335 | h10335
          · linarith only [h10335, h9666, hlam]
          · rcases p10290_3 (m.d 0 2) (by simp) with h10337 | h10337
            · rcases p10290_3 (m.d 0 3) (by simp) with h10338 | h10338
              · rcases p10290_3 (m.d 0 4) (by simp) with h10339 | h10339
                · rcases p10290_3 (m.d 0 5) (by simp) with h10340 | h10340
                  · rcases h2bigk with h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c | h10341c
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h0, hlam, p10341_1]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      rcases p10341_3 (m.d 0 2) (by simp) with h10344 | h10344
                      · rcases p10341_3 (m.d 1 2) (by simp) with h10345 | h10345
                        · rcases p10341_3 (m.d 2 3) (by simp) with h10346 | h10346
                          · linarith only [h10346, hlam, p10341_0]
                          · rcases p10341_3 (m.d 2 4) (by simp) with h10348 | h10348
                            · linarith only [h10348, h9887, hlam]
                            · rcases p10341_3 (m.d 2 5) (by simp) with h10350 | h10350
                              · linarith only [h10350, h9888, hlam]
                              · linarith only [h10350, h9899, hlam]
                        · linarith only [h10345, h9892, hlam]
                      · linarith only [h10344, hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      rcases p10341_3 (m.d 0 2) (by simp) with h10355 | h10355
                      · rcases p10341_3 (m.d 1 2) (by simp) with h10356 | h10356
                        · rcases p10341_3 (m.d 2 3) (by simp) with h10357 | h10357
                          · linarith only [h10357, h9886, hlam]
                          · linarith only [h10357, h9898, hlam]
                        · linarith only [h10356, h9893, hlam]
                      · linarith only [h10355, hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      rcases p10341_3 (m.d 0 2) (by simp) with h10362 | h10362
                      · rcases p10341_3 (m.d 1 2) (by simp) with h10363 | h10363
                        · rcases p10341_3 (m.d 2 3) (by simp) with h10364 | h10364
                          · linarith only [h10364, h9886, hlam]
                          · rcases p10341_3 (m.d 2 4) (by simp) with h10366 | h10366
                            · linarith only [h10366, h9887, hlam]
                            · rcases p10341_3 (m.d 2 5) (by simp) with h10368 | h10368
                              · linarith only [h10368, hlam, p10341_0]
                              · rcases h3bigk with h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c | h10370c
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h7600, hlam, p10370_1]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  rcases p10370_3 (m.d 0 3) (by simp) with h10373 | h10373
                                  · rcases p10370_3 (m.d 1 3) (by simp) with h10374 | h10374
                                    · rcases p10370_3 (m.d 2 3) (by simp) with h10375 | h10375
                                      · linarith only [h10375, h9886, hlam]
                                      · rcases p10370_3 (m.d 3 4) (by simp) with h10377 | h10377
                                        · linarith only [h10377, h9889, hlam]
                                        · rcases p10370_3 (m.d 3 5) (by simp) with h10379 | h10379
                                          · linarith only [h10379, h9890, hlam]
                                          · linarith only [h10379, h9899, hlam]
                                    · linarith only [h10374, h9892, hlam]
                                  · linarith only [h10373, h9886, hlam]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9890, h9898, h9899, hlam, p10370_2]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9898, h9899, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10370_1]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9890, h9892, h9898, h9899, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10370_1]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  rcases p10370_3 (m.d 0 3) (by simp) with h10388 | h10388
                                  · linarith only [h10388, h7600, hlam]
                                  · linarith only [h10388, h9886, hlam]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h10288, h7600, h9889, h9891, h9898, h9899, hlam, p10370_2]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9898, h9899, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10370_1]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9886, hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9892, hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h10288, h9889, h9891, h9899, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10370_1]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9899, hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9889, hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9895, hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9898, hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h10288, hlam, p10370_1]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9890, hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h9896, hlam, p10370_0]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [h0, h10288, h9886, h9889, h9891, h9898, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10370_1]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  rcases p10370_3 (m.d 0 3) (by simp) with h10406 | h10406
                                  · rcases p10370_3 (m.d 1 3) (by simp) with h10407 | h10407
                                    · rcases p10370_3 (m.d 2 3) (by simp) with h10408 | h10408
                                      · linarith only [h10408, h9899, hlam]
                                      · linarith only [h10408, h9898, hlam]
                                    · linarith only [h10407, h9895, hlam]
                                  · linarith only [h10406, h9889, hlam]
                                · have p10370_0 := h10370c.1
                                  have p10370_1 := h10370c.2.1
                                  have p10370_2 := h10370c.2.2.1
                                  have p10370_3 := h10370c.2.2.2
                                  linarith only [hlam, p10370_0]
                        · linarith only [h10363, h9894, hlam]
                      · linarith only [h10362, hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h10288, h9886, h9889, h9891, hc12, hlam, hphi, ht01, ht0b, ht5b, p10341_1, u5ehi3]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      rcases p10341_3 (m.d 0 2) (by simp) with h10418 | h10418
                      · linarith only [h0, h10418, hlam]
                      · linarith only [h10418, h9886, hlam]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      rcases p10341_3 (m.d 0 2) (by simp) with h10421 | h10421
                      · linarith only [h0, h10421, hlam]
                      · linarith only [h10421, h9887, hlam]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      rcases p10341_3 (m.d 0 2) (by simp) with h10424 | h10424
                      · linarith only [h0, h10424, hlam]
                      · linarith only [h10424, h9888, hlam]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h9886, hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h9892, hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h10288, h9886, h9889, h9891, h9899, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p10341_1]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h9899, hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h9887, hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h9893, hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h9898, hlam, p10341_1]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h10286, hlam, p10341_1]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h9888, hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h9894, hlam, p10341_0]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [h0, h9888, h9898, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10341_1]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      rcases p10341_3 (m.d 0 2) (by simp) with h10440 | h10440
                      · rcases p10341_3 (m.d 1 2) (by simp) with h10441 | h10441
                        · rcases p10341_3 (m.d 2 3) (by simp) with h10442 | h10442
                          · linarith only [h10442, h9899, hlam]
                          · linarith only [h10442, h9898, hlam]
                        · linarith only [h10441, h9893, hlam]
                      · linarith only [h10440, h9887, hlam]
                    · have p10341_0 := h10341c.1
                      have p10341_1 := h10341c.2.1
                      have p10341_2 := h10341c.2.2.1
                      have p10341_3 := h10341c.2.2.2
                      linarith only [hlam, p10341_0]
                  · linarith only [h10340, h9666, hlam]
                · linarith only [h10339, h8836, hlam]
              · linarith only [h10338, h7600, hlam]
            · linarith only [h0, h10337, hlam]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h9888, hlam, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h9890, hlam, p10290_0]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [h9891, hlam, p10290_1]
        · have p10290_0 := h10290c.1
          have p10290_1 := h10290c.2.1
          have p10290_2 := h10290c.2.2.1
          have p10290_3 := h10290c.2.2.2
          linarith only [hlam, p10290_0]

set_option maxHeartbeats 6000000 in
set_option maxHeartbeats 6000000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s17_x0_x0_x0_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg9889 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9890 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9891 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9892 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9893 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9894 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9895 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9896 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h9897 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h9898 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h10456 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  have h9889 := hg9889
  linarith only [h0, h10456, h9886, h9889, h9898, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]

end R2N4
