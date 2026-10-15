import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9970 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9972 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  linarith only [h0, h9029, h9972, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9970 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9972 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h9974 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9975 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h9976 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 2 3 4 (by decide) (by decide) with h9977 | h9977
  · rcases m.htr 2 3 5 (by decide) (by decide) with h9978 | h9978
    · rcases m.htr 2 4 5 (by decide) (by decide) with h9979 | h9979
      · rcases m.htr 3 4 5 (by decide) (by decide) with h9980 | h9980
        · rcases h0bigk with h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c | h9981c
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [hlam, p9981_0]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            rcases p9981_3 (m.d 0 1) (by simp) with h9983 | h9983
            · rcases p9981_3 (m.d 0 2) (by simp) with h9984 | h9984
              · linarith only [h0, h9984, hlam]
              · rcases p9981_3 (m.d 0 3) (by simp) with h9986 | h9986
                · linarith only [h1, h9986, hlam]
                · linarith only [h4, h9986, hlam]
            · linarith only [h0, h9983, hlam]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [h1, h9974, h9980, hc01, hc45, hlam, hphi, ht0b, ht5b, p9981_1]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            rcases p9981_3 (m.d 0 1) (by simp) with h9991 | h9991
            · rcases p9981_3 (m.d 0 2) (by simp) with h9992 | h9992
              · linarith only [h0, h9992, hlam]
              · rcases p9981_3 (m.d 0 3) (by simp) with h9994 | h9994
                · linarith only [h1, h9994, hlam]
                · linarith only [h9965, h9994, hlam]
            · linarith only [h2, h9991, hlam]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            rcases p9981_3 (m.d 0 1) (by simp) with h9998 | h9998
            · rcases p9981_3 (m.d 0 2) (by simp) with h9999 | h9999
              · linarith only [h0, h9999, hlam]
              · rcases p9981_3 (m.d 0 3) (by simp) with h10001 | h10001
                · linarith only [h1, h10001, hlam]
                · linarith only [h10001, h9966, hlam]
            · linarith only [h3, h9998, hlam]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [h0, hlam, p9981_0]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [hlam, p9981_0]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [h4, hlam, p9981_0]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [h7821, hlam, p9981_1]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [h9029, hlam, p9981_0]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [h1, hlam, p9981_1]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            rcases p9981_3 (m.d 0 1) (by simp) with h10011 | h10011
            · rcases p9981_3 (m.d 0 2) (by simp) with h10012 | h10012
              · linarith only [h10012, h4, hlam]
              · rcases p9981_3 (m.d 0 3) (by simp) with h10014 | h10014
                · rcases p9981_3 (m.d 0 4) (by simp) with h10015 | h10015
                  · linarith only [h10015, h9965, hlam]
                  · linarith only [h10015, h7821, hlam]
                · linarith only [h10014, h4, hlam]
            · linarith only [h0, h10011, hlam]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [hlam, p9981_0]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            rcases p9981_3 (m.d 0 1) (by simp) with h10021 | h10021
            · rcases p9981_3 (m.d 0 2) (by simp) with h10022 | h10022
              · linarith only [h10022, h4, hlam]
              · rcases p9981_3 (m.d 0 3) (by simp) with h10024 | h10024
                · rcases p9981_3 (m.d 0 4) (by simp) with h10025 | h10025
                  · linarith only [h10025, h9965, hlam]
                  · rcases p9981_3 (m.d 0 5) (by simp) with h10027 | h10027
                    · linarith only [h10027, h9966, hlam]
                    · rcases h2bigk with h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c | h10029c
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h4, h9029, h9967, hc12, hc23, hlam, hphi, p10029_1, p9981_1]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h4, hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h7821, hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h9029, hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h0, hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h9968, hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h9970, hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h9972, hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        rcases p10029_3 (m.d 0 2) (by simp) with h10040 | h10040
                        · linarith only [h10040, hlam, p10029_0]
                        · rcases p10029_3 (m.d 1 2) (by simp) with h10042 | h10042
                          · linarith only [h10042, h9968, hlam]
                          · rcases p10029_3 (m.d 2 3) (by simp) with h10044 | h10044
                            · rcases p10029_3 (m.d 2 4) (by simp) with h10045 | h10045
                              · linarith only [h10045, h9977, hlam]
                              · linarith only [h10045, h7821, hlam]
                            · linarith only [h10044, hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        rcases p10029_3 (m.d 0 2) (by simp) with h10049 | h10049
                        · linarith only [h10049, h4, hlam]
                        · linarith only [h0, h10049, hlam]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h9029, h9979, hc02, hc23, hlam, hphi, p10029_1]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h0, h9029, hc12, hc23, hlam, hphi, p10029_1]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        rcases p10029_3 (m.d 0 2) (by simp) with h10055 | h10055
                        · linarith only [h10055, hlam, p10029_0]
                        · rcases p10029_3 (m.d 1 2) (by simp) with h10057 | h10057
                          · linarith only [h10057, h9970, hlam]
                          · rcases p10029_3 (m.d 2 3) (by simp) with h10059 | h10059
                            · rcases p10029_3 (m.d 2 4) (by simp) with h10060 | h10060
                              · rcases p10029_3 (m.d 2 5) (by simp) with h10061 | h10061
                                · linarith only [h10061, h9979, hlam]
                                · linarith only [h10061, h9029, hlam]
                              · linarith only [h10060, hlam, p10029_0]
                            · linarith only [h10059, h4, hlam]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        rcases p10029_3 (m.d 0 2) (by simp) with h10066 | h10066
                        · linarith only [h10066, h7821, hlam]
                        · linarith only [h0, h10066, hlam]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h9977, hlam, p10029_1]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h0, h9029, hc12, hc24, hlam, hphi, p10029_1]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        rcases p10029_3 (m.d 0 2) (by simp) with h10072 | h10072
                        · linarith only [h10072, hlam, p10029_0]
                        · rcases p10029_3 (m.d 1 2) (by simp) with h10074 | h10074
                          · linarith only [h10074, h9972, hlam]
                          · rcases p10029_3 (m.d 2 3) (by simp) with h10076 | h10076
                            · rcases p10029_3 (m.d 2 4) (by simp) with h10077 | h10077
                              · rcases p10029_3 (m.d 2 5) (by simp) with h10078 | h10078
                                · rcases h3bigk with h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c | h10079c
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h4, h9974, h9980, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10079_1]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h4, hlam, p10079_1]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    rcases p10079_3 (m.d 0 3) (by simp) with h10083 | h10083
                                    · rcases p10079_3 (m.d 1 3) (by simp) with h10084 | h10084
                                      · linarith only [h1, h10084, hlam]
                                      · linarith only [h10084, h9974, hlam]
                                    · linarith only [h10083, hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    rcases p10079_3 (m.d 0 3) (by simp) with h10088 | h10088
                                    · rcases p10079_3 (m.d 1 3) (by simp) with h10089 | h10089
                                      · linarith only [h1, h10089, hlam]
                                      · linarith only [h10089, h9975, hlam]
                                    · linarith only [h10088, hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h1, hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h9968, hlam, p10079_1]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h1, h9980, hc01, hc45, hlam, hphi, ht0b, ht5b, p10079_1]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    rcases p10079_3 (m.d 0 3) (by simp) with h10097 | h10097
                                    · rcases p10079_3 (m.d 1 3) (by simp) with h10098 | h10098
                                      · rcases p10079_3 (m.d 2 3) (by simp) with h10099 | h10099
                                        · rcases p10079_3 (m.d 3 4) (by simp) with h10100 | h10100
                                          · linarith only [h10100, h9974, hlam]
                                          · linarith only [h10100, h9980, hlam]
                                        · linarith only [h10099, h9978, hlam]
                                      · linarith only [h10098, hlam, p10079_0]
                                    · linarith only [h10097, h9966, hlam]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10079_1, p9981_1]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h9974, h9980, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10079_1]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    rcases p10079_3 (m.d 0 3) (by simp) with h10109 | h10109
                                    · linarith only [h10109, h4, hlam]
                                    · linarith only [h10109, h9965, hlam]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    rcases p10079_3 (m.d 0 3) (by simp) with h10112 | h10112
                                    · linarith only [h10112, h4, hlam]
                                    · linarith only [h10112, h9966, hlam]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h9965, hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h9974, hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h9977, hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h2, h9974, hc03, hc35, hlam, hphi, ht0b, ht5b, p10079_1, p9981_1]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h9966, hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h9975, hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h9978, hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [h9980, hlam, p10079_0]
                                  · have p10079_0 := h10079c.1
                                    have p10079_1 := h10079c.2.1
                                    have p10079_2 := h10079c.2.2.1
                                    have p10079_3 := h10079c.2.2.2
                                    linarith only [hlam, p10079_0]
                                · linarith only [h10078, hlam, p10029_0]
                              · linarith only [h10077, h7821, hlam]
                            · linarith only [h10076, h4, hlam]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        rcases p10029_3 (m.d 0 2) (by simp) with h10128 | h10128
                        · linarith only [h10128, h9029, hlam]
                        · linarith only [h0, h10128, hlam]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h9978, hlam, p10029_1]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [h9979, hlam, p10029_0]
                      · have p10029_0 := h10029c.1
                        have p10029_1 := h10029c.2.1
                        have p10029_2 := h10029c.2.2.1
                        have p10029_3 := h10029c.2.2.2
                        linarith only [hlam, p10029_0]
                · linarith only [h10024, h9965, hlam]
            · linarith only [h10021, h2, hlam]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            rcases p9981_3 (m.d 0 1) (by simp) with h10136 | h10136
            · rcases p9981_3 (m.d 0 2) (by simp) with h10137 | h10137
              · linarith only [h10137, h4, hlam]
              · rcases p9981_3 (m.d 0 3) (by simp) with h10139 | h10139
                · rcases p9981_3 (m.d 0 4) (by simp) with h10140 | h10140
                  · linarith only [h10140, h9965, hlam]
                  · linarith only [h10140, h9967, hlam]
                · linarith only [h10139, h9966, hlam]
            · linarith only [h10136, h3, hlam]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [h2, hlam, p9981_0]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            rcases p9981_3 (m.d 0 1) (by simp) with h10146 | h10146
            · rcases p9981_3 (m.d 0 2) (by simp) with h10147 | h10147
              · linarith only [h10147, h7821, hlam]
              · rcases p9981_3 (m.d 0 3) (by simp) with h10149 | h10149
                · rcases p9981_3 (m.d 0 4) (by simp) with h10150 | h10150
                  · rcases p9981_3 (m.d 0 5) (by simp) with h10151 | h10151
                    · linarith only [h10151, h9967, hlam]
                    · linarith only [h10151, h9029, hlam]
                  · linarith only [h10150, h7821, hlam]
                · linarith only [h10149, h4, hlam]
            · linarith only [h0, h10146, hlam]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [h9965, hlam, p9981_0]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [hlam, p9981_0]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            rcases p9981_3 (m.d 0 1) (by simp) with h10159 | h10159
            · rcases p9981_3 (m.d 0 2) (by simp) with h10160 | h10160
              · linarith only [h10160, h7821, hlam]
              · rcases p9981_3 (m.d 0 3) (by simp) with h10162 | h10162
                · rcases p9981_3 (m.d 0 4) (by simp) with h10163 | h10163
                  · rcases p9981_3 (m.d 0 5) (by simp) with h10164 | h10164
                    · linarith only [h10164, h9967, hlam]
                    · rcases h2bigk with h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c | h10166c
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h4, hc12, hc23, hlam, hphi, p10166_1]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h4, hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h7821, hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h9029, hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h0, hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h9968, hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h9970, hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h9972, hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        rcases p10166_3 (m.d 0 2) (by simp) with h10177 | h10177
                        · linarith only [h10177, hlam, p10166_0]
                        · rcases p10166_3 (m.d 1 2) (by simp) with h10179 | h10179
                          · linarith only [h10179, h9968, hlam]
                          · rcases p10166_3 (m.d 2 3) (by simp) with h10181 | h10181
                            · rcases p10166_3 (m.d 2 4) (by simp) with h10182 | h10182
                              · linarith only [h10182, h9977, hlam]
                              · linarith only [h10182, h7821, hlam]
                            · linarith only [h10181, hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        rcases p10166_3 (m.d 0 2) (by simp) with h10186 | h10186
                        · linarith only [h10186, h4, hlam]
                        · linarith only [h0, h10186, hlam]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h7821, hc02, hc23, hlam, hphi, p10166_1]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h0, h9029, hc12, hc23, hlam, hphi, p10166_1]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        rcases p10166_3 (m.d 0 2) (by simp) with h10192 | h10192
                        · linarith only [h10192, hlam, p10166_0]
                        · rcases p10166_3 (m.d 1 2) (by simp) with h10194 | h10194
                          · linarith only [h10194, h9970, hlam]
                          · rcases p10166_3 (m.d 2 3) (by simp) with h10196 | h10196
                            · rcases p10166_3 (m.d 2 4) (by simp) with h10197 | h10197
                              · rcases p10166_3 (m.d 2 5) (by simp) with h10198 | h10198
                                · linarith only [h10198, h9979, hlam]
                                · linarith only [h10198, h9029, hlam]
                              · linarith only [h10197, hlam, p10166_0]
                            · linarith only [h10196, h4, hlam]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        rcases p10166_3 (m.d 0 2) (by simp) with h10203 | h10203
                        · linarith only [h10203, h7821, hlam]
                        · linarith only [h0, h10203, hlam]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h9977, hlam, p10166_1]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h0, h9029, hc12, hc24, hlam, hphi, p10166_1]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        rcases p10166_3 (m.d 0 2) (by simp) with h10209 | h10209
                        · linarith only [h10209, hlam, p10166_0]
                        · rcases p10166_3 (m.d 1 2) (by simp) with h10211 | h10211
                          · linarith only [h10211, h9972, hlam]
                          · rcases p10166_3 (m.d 2 3) (by simp) with h10213 | h10213
                            · rcases p10166_3 (m.d 2 4) (by simp) with h10214 | h10214
                              · rcases p10166_3 (m.d 2 5) (by simp) with h10215 | h10215
                                · rcases h3bigk with h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c | h10216c
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h4, h9974, h9980, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10216_1]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h4, hlam, p10216_1]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    rcases p10216_3 (m.d 0 3) (by simp) with h10220 | h10220
                                    · rcases p10216_3 (m.d 1 3) (by simp) with h10221 | h10221
                                      · linarith only [h1, h10221, hlam]
                                      · linarith only [h10221, h9974, hlam]
                                    · linarith only [h10220, hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    rcases p10216_3 (m.d 0 3) (by simp) with h10225 | h10225
                                    · rcases p10216_3 (m.d 1 3) (by simp) with h10226 | h10226
                                      · linarith only [h1, h10226, hlam]
                                      · linarith only [h10226, h9975, hlam]
                                    · linarith only [h10225, hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h1, hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h9968, hlam, p10216_1]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h1, h9980, hc01, hc45, hlam, hphi, ht0b, ht5b, p10216_1]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    rcases p10216_3 (m.d 0 3) (by simp) with h10234 | h10234
                                    · rcases p10216_3 (m.d 1 3) (by simp) with h10235 | h10235
                                      · rcases p10216_3 (m.d 2 3) (by simp) with h10236 | h10236
                                        · rcases p10216_3 (m.d 3 4) (by simp) with h10237 | h10237
                                          · linarith only [h10237, h9974, hlam]
                                          · linarith only [h10237, h9980, hlam]
                                        · linarith only [h10236, h9978, hlam]
                                      · linarith only [h10235, hlam, p10216_0]
                                    · linarith only [h10234, h9966, hlam]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h9965, h9980, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10216_1]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h9974, h9980, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10216_1]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    rcases p10216_3 (m.d 0 3) (by simp) with h10246 | h10246
                                    · linarith only [h10246, h4, hlam]
                                    · linarith only [h10246, h9965, hlam]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    rcases p10216_3 (m.d 0 3) (by simp) with h10249 | h10249
                                    · linarith only [h10249, h4, hlam]
                                    · linarith only [h10249, h9966, hlam]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h9965, hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h9974, hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h9977, hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h1, h9974, hc01, hc35, hlam, hphi, ht0b, ht5b, p10216_1]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h9966, hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h9975, hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h9978, hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [h9980, hlam, p10216_0]
                                  · have p10216_0 := h10216c.1
                                    have p10216_1 := h10216c.2.1
                                    have p10216_2 := h10216c.2.2.1
                                    have p10216_3 := h10216c.2.2.2
                                    linarith only [hlam, p10216_0]
                                · linarith only [h10215, hlam, p10166_0]
                              · linarith only [h10214, h7821, hlam]
                            · linarith only [h10213, h4, hlam]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        rcases p10166_3 (m.d 0 2) (by simp) with h10265 | h10265
                        · linarith only [h10265, h9029, hlam]
                        · linarith only [h0, h10265, hlam]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h9978, hlam, p10166_1]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [h9979, hlam, p10166_0]
                      · have p10166_0 := h10166c.1
                        have p10166_1 := h10166c.2.1
                        have p10166_2 := h10166c.2.2.1
                        have p10166_3 := h10166c.2.2.2
                        linarith only [hlam, p10166_0]
                  · linarith only [h10163, h9967, hlam]
                · linarith only [h10162, h9966, hlam]
            · linarith only [h10159, h3, hlam]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [h3, hlam, p9981_0]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            rcases p9981_3 (m.d 0 1) (by simp) with h10275 | h10275
            · rcases p9981_3 (m.d 0 2) (by simp) with h10276 | h10276
              · linarith only [h10276, h9029, hlam]
              · rcases p9981_3 (m.d 0 3) (by simp) with h10278 | h10278
                · rcases p9981_3 (m.d 0 4) (by simp) with h10279 | h10279
                  · rcases p9981_3 (m.d 0 5) (by simp) with h10280 | h10280
                    · rcases h2bigk with h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c | h10281c
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10281_1, p9981_1]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h4, hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h7821, hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h9029, hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h0, hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h9968, hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h9970, hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h9972, hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        rcases p10281_3 (m.d 0 2) (by simp) with h10292 | h10292
                        · linarith only [h10292, hlam, p10281_0]
                        · rcases p10281_3 (m.d 1 2) (by simp) with h10294 | h10294
                          · linarith only [h10294, h9968, hlam]
                          · rcases p10281_3 (m.d 2 3) (by simp) with h10296 | h10296
                            · rcases p10281_3 (m.d 2 4) (by simp) with h10297 | h10297
                              · linarith only [h10297, h9977, hlam]
                              · linarith only [h10297, h7821, hlam]
                            · linarith only [h10296, hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        rcases p10281_3 (m.d 0 2) (by simp) with h10301 | h10301
                        · linarith only [h10301, h4, hlam]
                        · linarith only [h0, h10301, hlam]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h7821, hc02, hc23, hlam, hphi, p10281_1]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h0, h9029, hc12, hc23, hlam, hphi, p10281_1, p9981_1]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        rcases p10281_3 (m.d 0 2) (by simp) with h10307 | h10307
                        · linarith only [h10307, hlam, p10281_0]
                        · rcases p10281_3 (m.d 1 2) (by simp) with h10309 | h10309
                          · linarith only [h10309, h9970, hlam]
                          · rcases p10281_3 (m.d 2 3) (by simp) with h10311 | h10311
                            · rcases p10281_3 (m.d 2 4) (by simp) with h10312 | h10312
                              · rcases p10281_3 (m.d 2 5) (by simp) with h10313 | h10313
                                · linarith only [h10313, h9979, hlam]
                                · linarith only [h10313, h9029, hlam]
                              · linarith only [h10312, hlam, p10281_0]
                            · linarith only [h10311, h4, hlam]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        rcases p10281_3 (m.d 0 2) (by simp) with h10318 | h10318
                        · linarith only [h10318, h7821, hlam]
                        · linarith only [h0, h10318, hlam]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h9977, hlam, p10281_1]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h0, h9029, hc12, hc24, hlam, hphi, p10281_1, p9981_1]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        rcases p10281_3 (m.d 0 2) (by simp) with h10324 | h10324
                        · linarith only [h10324, hlam, p10281_0]
                        · rcases p10281_3 (m.d 1 2) (by simp) with h10326 | h10326
                          · linarith only [h10326, h9972, hlam]
                          · rcases p10281_3 (m.d 2 3) (by simp) with h10328 | h10328
                            · rcases p10281_3 (m.d 2 4) (by simp) with h10329 | h10329
                              · rcases p10281_3 (m.d 2 5) (by simp) with h10330 | h10330
                                · rcases h3bigk with h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c | h10331c
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h4, h9974, h9980, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10331_1]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h4, hlam, p10331_1]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    rcases p10331_3 (m.d 0 3) (by simp) with h10335 | h10335
                                    · rcases p10331_3 (m.d 1 3) (by simp) with h10336 | h10336
                                      · linarith only [h1, h10336, hlam]
                                      · linarith only [h10336, h9974, hlam]
                                    · linarith only [h10335, hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    rcases p10331_3 (m.d 0 3) (by simp) with h10340 | h10340
                                    · rcases p10331_3 (m.d 1 3) (by simp) with h10341 | h10341
                                      · linarith only [h1, h10341, hlam]
                                      · linarith only [h10341, h9975, hlam]
                                    · linarith only [h10340, hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h1, hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h9968, hlam, p10331_1]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h1, h9980, hc01, hc45, hlam, hphi, ht0b, ht5b, p10331_1]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    rcases p10331_3 (m.d 0 3) (by simp) with h10349 | h10349
                                    · rcases p10331_3 (m.d 1 3) (by simp) with h10350 | h10350
                                      · rcases p10331_3 (m.d 2 3) (by simp) with h10351 | h10351
                                        · rcases p10331_3 (m.d 3 4) (by simp) with h10352 | h10352
                                          · linarith only [h10352, h9974, hlam]
                                          · linarith only [h10352, h9980, hlam]
                                        · linarith only [h10351, h9978, hlam]
                                      · linarith only [h10350, hlam, p10331_0]
                                    · linarith only [h10349, h9966, hlam]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h9965, h9980, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10331_1]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h9974, h9980, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10331_1]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    rcases p10331_3 (m.d 0 3) (by simp) with h10361 | h10361
                                    · linarith only [h10361, h4, hlam]
                                    · linarith only [h10361, h9965, hlam]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    rcases p10331_3 (m.d 0 3) (by simp) with h10364 | h10364
                                    · linarith only [h10364, h4, hlam]
                                    · linarith only [h10364, h9966, hlam]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h9965, hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h9974, hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h9977, hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h1, h9974, hc01, hc35, hlam, hphi, ht0b, ht5b, p10331_1]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h9966, hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h9975, hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h9978, hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [h9980, hlam, p10331_0]
                                  · have p10331_0 := h10331c.1
                                    have p10331_1 := h10331c.2.1
                                    have p10331_2 := h10331c.2.2.1
                                    have p10331_3 := h10331c.2.2.2
                                    linarith only [hlam, p10331_0]
                                · linarith only [h10330, hlam, p10281_0]
                              · linarith only [h10329, h7821, hlam]
                            · linarith only [h10328, h4, hlam]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        rcases p10281_3 (m.d 0 2) (by simp) with h10380 | h10380
                        · linarith only [h10380, h9029, hlam]
                        · linarith only [h0, h10380, hlam]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h9978, hlam, p10281_1]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [h9979, hlam, p10281_0]
                      · have p10281_0 := h10281c.1
                        have p10281_1 := h10281c.2.1
                        have p10281_2 := h10281c.2.2.1
                        have p10281_3 := h10281c.2.2.2
                        linarith only [hlam, p10281_0]
                    · linarith only [h10280, h9029, hlam]
                  · linarith only [h10279, h7821, hlam]
                · linarith only [h10278, h4, hlam]
            · linarith only [h0, h10275, hlam]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [h9966, hlam, p9981_0]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [h9967, hlam, p9981_1]
          · have p9981_0 := h9981c.1
            have p9981_1 := h9981c.2.1
            have p9981_2 := h9981c.2.2.1
            have p9981_3 := h9981c.2.2.2
            linarith only [hlam, p9981_0]
        · rcases h0bigk with h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c | h10393c
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [hlam, p10393_0]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            rcases p10393_3 (m.d 0 1) (by simp) with h10395 | h10395
            · rcases p10393_3 (m.d 0 2) (by simp) with h10396 | h10396
              · linarith only [h0, h10396, hlam]
              · rcases p10393_3 (m.d 0 3) (by simp) with h10398 | h10398
                · linarith only [h1, h10398, hlam]
                · linarith only [h10398, h4, hlam]
            · linarith only [h0, h10395, hlam]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h9965, h9967, h9980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10393_1]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h9967, h9980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10393_1]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            rcases p10393_3 (m.d 0 1) (by simp) with h10404 | h10404
            · rcases p10393_3 (m.d 0 2) (by simp) with h10405 | h10405
              · linarith only [h0, h10405, hlam]
              · rcases p10393_3 (m.d 0 3) (by simp) with h10407 | h10407
                · linarith only [h1, h10407, hlam]
                · linarith only [h10407, h9966, hlam]
            · linarith only [h10404, h3, hlam]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h0, hlam, p10393_0]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [hlam, p10393_0]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h4, hlam, p10393_0]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h7821, hlam, p10393_1]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h9029, hlam, p10393_0]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h1, hlam, p10393_1]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            rcases p10393_3 (m.d 0 1) (by simp) with h10417 | h10417
            · rcases p10393_3 (m.d 0 2) (by simp) with h10418 | h10418
              · linarith only [h10418, h4, hlam]
              · rcases p10393_3 (m.d 0 3) (by simp) with h10420 | h10420
                · rcases p10393_3 (m.d 0 4) (by simp) with h10421 | h10421
                  · linarith only [h10421, h9965, hlam]
                  · linarith only [h10421, h7821, hlam]
                · linarith only [h10420, h4, hlam]
            · linarith only [h0, h10417, hlam]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [hlam, p10393_0]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h2, h9976, h9980, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10393_1]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            rcases p10393_3 (m.d 0 1) (by simp) with h10428 | h10428
            · rcases p10393_3 (m.d 0 2) (by simp) with h10429 | h10429
              · linarith only [h10429, h4, hlam]
              · rcases p10393_3 (m.d 0 3) (by simp) with h10431 | h10431
                · rcases p10393_3 (m.d 0 4) (by simp) with h10432 | h10432
                  · linarith only [h10432, h9965, hlam]
                  · linarith only [h10432, h9967, hlam]
                · linarith only [h10431, h9966, hlam]
            · linarith only [h10428, h3, hlam]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h2, hlam, p10393_0]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            rcases p10393_3 (m.d 0 1) (by simp) with h10438 | h10438
            · rcases p10393_3 (m.d 0 2) (by simp) with h10439 | h10439
              · linarith only [h10439, h7821, hlam]
              · rcases p10393_3 (m.d 0 3) (by simp) with h10441 | h10441
                · rcases p10393_3 (m.d 0 4) (by simp) with h10442 | h10442
                  · rcases p10393_3 (m.d 0 5) (by simp) with h10443 | h10443
                    · linarith only [h10443, h9967, hlam]
                    · linarith only [h10443, h9029, hlam]
                  · linarith only [h10442, h7821, hlam]
                · linarith only [h10441, h4, hlam]
            · linarith only [h0, h10438, hlam]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h9965, hlam, p10393_0]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [hlam, p10393_0]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            rcases p10393_3 (m.d 0 1) (by simp) with h10451 | h10451
            · rcases p10393_3 (m.d 0 2) (by simp) with h10452 | h10452
              · linarith only [h10452, h7821, hlam]
              · rcases p10393_3 (m.d 0 3) (by simp) with h10454 | h10454
                · rcases p10393_3 (m.d 0 4) (by simp) with h10455 | h10455
                  · rcases p10393_3 (m.d 0 5) (by simp) with h10456 | h10456
                    · linarith only [h10456, h9967, hlam]
                    · rcases h2bigk with h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c | h10458c
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h9029, hc12, hc25, hlam, hphi, p10458_1]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h4, hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h7821, hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h9029, hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h0, hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h9968, hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h9970, hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h9972, hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        rcases p10458_3 (m.d 0 2) (by simp) with h10469 | h10469
                        · linarith only [h10469, hlam, p10458_0]
                        · rcases p10458_3 (m.d 1 2) (by simp) with h10471 | h10471
                          · linarith only [h10471, h9968, hlam]
                          · rcases p10458_3 (m.d 2 3) (by simp) with h10473 | h10473
                            · rcases p10458_3 (m.d 2 4) (by simp) with h10474 | h10474
                              · linarith only [h10474, h9977, hlam]
                              · linarith only [h10474, h7821, hlam]
                            · linarith only [h10473, hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        rcases p10458_3 (m.d 0 2) (by simp) with h10478 | h10478
                        · linarith only [h10478, h4, hlam]
                        · linarith only [h0, h10478, hlam]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h3, h7821, h9976, h9980, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10393_1, p10458_1]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h9029, hc02, hc23, hlam, hphi, p10458_1]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        rcases p10458_3 (m.d 0 2) (by simp) with h10484 | h10484
                        · linarith only [h10484, hlam, p10458_0]
                        · rcases p10458_3 (m.d 1 2) (by simp) with h10486 | h10486
                          · linarith only [h10486, h9970, hlam]
                          · rcases p10458_3 (m.d 2 3) (by simp) with h10488 | h10488
                            · rcases p10458_3 (m.d 2 4) (by simp) with h10489 | h10489
                              · rcases p10458_3 (m.d 2 5) (by simp) with h10490 | h10490
                                · linarith only [h10490, h9979, hlam]
                                · linarith only [h10490, h9029, hlam]
                              · linarith only [h10489, hlam, p10458_0]
                            · linarith only [h10488, h4, hlam]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        rcases p10458_3 (m.d 0 2) (by simp) with h10495 | h10495
                        · linarith only [h10495, h7821, hlam]
                        · linarith only [h0, h10495, hlam]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h9977, hlam, p10458_1]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h0, h9029, hc12, hc24, hlam, hphi, p10458_1]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        rcases p10458_3 (m.d 0 2) (by simp) with h10501 | h10501
                        · linarith only [h10501, hlam, p10458_0]
                        · rcases p10458_3 (m.d 1 2) (by simp) with h10503 | h10503
                          · linarith only [h10503, h9972, hlam]
                          · rcases p10458_3 (m.d 2 3) (by simp) with h10505 | h10505
                            · rcases p10458_3 (m.d 2 4) (by simp) with h10506 | h10506
                              · rcases p10458_3 (m.d 2 5) (by simp) with h10507 | h10507
                                · rcases h3bigk with h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c | h10508c
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h9974, h9976, h9980, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10508_1]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h4, hlam, p10508_1]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h3, h9965, h9976, h9980, hlam, p10393_1, p10508_2]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    rcases p10508_3 (m.d 0 3) (by simp) with h10513 | h10513
                                    · rcases p10508_3 (m.d 1 3) (by simp) with h10514 | h10514
                                      · linarith only [h1, h10514, hlam]
                                      · linarith only [h10514, h9975, hlam]
                                    · linarith only [h10513, hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h1, hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h9968, hlam, p10508_1]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    rcases p10508_3 (m.d 0 3) (by simp) with h10521 | h10521
                                    · rcases p10508_3 (m.d 1 3) (by simp) with h10522 | h10522
                                      · rcases p10508_3 (m.d 2 3) (by simp) with h10523 | h10523
                                        · rcases p10508_3 (m.d 3 4) (by simp) with h10524 | h10524
                                          · linarith only [h10524, hlam, p10508_0]
                                          · rcases p10508_3 (m.d 3 5) (by simp) with h10526 | h10526
                                            · linarith only [h10526, h9975, hlam]
                                            · linarith only [h10526, h9980, hlam]
                                        · linarith only [h10523, h9977, hlam]
                                      · linarith only [h10522, hlam, p10508_0]
                                    · linarith only [h10521, h9965, hlam]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    rcases p10508_3 (m.d 0 3) (by simp) with h10532 | h10532
                                    · rcases p10508_3 (m.d 1 3) (by simp) with h10533 | h10533
                                      · rcases p10508_3 (m.d 2 3) (by simp) with h10534 | h10534
                                        · rcases p10508_3 (m.d 3 4) (by simp) with h10535 | h10535
                                          · linarith only [h10535, h9974, hlam]
                                          · rcases p10508_3 (m.d 3 5) (by simp) with h10537 | h10537
                                            · linarith only [h10537, hlam, p10508_0]
                                            · rcases h5bigk with h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c | h10539c
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9965, h9976, h9980, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10393_1, p10539_1]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9029, hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h4, h9965, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p10393_1, p10539_1]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h4, h9965, h9980, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10393_1, p10539_1]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h3, hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9972, hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p10539_1]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h3, h4, h9965, h9980, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10393_1, p10539_1]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h0, h9029, hc12, hc25, hlam, hphi, p10539_1]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9972, hc12, hc25, hlam, hphi, p10539_1]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                rcases p10539_3 (m.d 0 5) (by simp) with h10553 | h10553
                                                · linarith only [h10553, h9029, hlam]
                                                · linarith only [h10553, h9966, hlam]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9977, h9979, h9980, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10539_1]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9966, hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9975, hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9978, hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9980, hlam, p10539_1]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9967, hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9976, hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9979, hlam, p10539_0]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [h9976, h9980, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10539_1]
                                              · have p10539_0 := h10539c.1
                                                have p10539_1 := h10539c.2.1
                                                have p10539_2 := h10539c.2.2.1
                                                have p10539_3 := h10539c.2.2.2
                                                linarith only [hlam, p10539_0]
                                        · linarith only [h10534, h9978, hlam]
                                      · linarith only [h10533, hlam, p10508_0]
                                    · linarith only [h10532, h9966, hlam]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h0, h9029, h9965, hc12, hc23, hlam, hphi, p10393_1, p10508_1]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h9974, h9976, h9980, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10508_1]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h4, h9965, h9967, h9980, hlam, p10393_1, p10508_2]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    rcases p10508_3 (m.d 0 3) (by simp) with h10574 | h10574
                                    · linarith only [h10574, h4, hlam]
                                    · linarith only [h10574, h9966, hlam]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h9965, hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h9974, hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h9977, hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h9980, hlam, p10508_1]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h9966, hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h9975, hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h9978, hlam, p10508_0]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [h4, h9965, h9966, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10393_1, p10508_1]
                                  · have p10508_0 := h10508c.1
                                    have p10508_1 := h10508c.2.1
                                    have p10508_2 := h10508c.2.2.1
                                    have p10508_3 := h10508c.2.2.2
                                    linarith only [hlam, p10508_0]
                                · linarith only [h10507, hlam, p10458_0]
                              · linarith only [h10506, h7821, hlam]
                            · linarith only [h10505, h4, hlam]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        rcases p10458_3 (m.d 0 2) (by simp) with h10590 | h10590
                        · linarith only [h10590, h9029, hlam]
                        · linarith only [h0, h10590, hlam]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h9978, hlam, p10458_1]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [h9979, hlam, p10458_0]
                      · have p10458_0 := h10458c.1
                        have p10458_1 := h10458c.2.1
                        have p10458_2 := h10458c.2.2.1
                        have p10458_3 := h10458c.2.2.2
                        linarith only [hlam, p10458_0]
                  · linarith only [h10455, h9967, hlam]
                · linarith only [h10454, h9966, hlam]
            · linarith only [h10451, h3, hlam]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h3, hlam, p10393_0]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            rcases p10393_3 (m.d 0 1) (by simp) with h10600 | h10600
            · rcases p10393_3 (m.d 0 2) (by simp) with h10601 | h10601
              · linarith only [h10601, h9029, hlam]
              · rcases p10393_3 (m.d 0 3) (by simp) with h10603 | h10603
                · rcases p10393_3 (m.d 0 4) (by simp) with h10604 | h10604
                  · rcases p10393_3 (m.d 0 5) (by simp) with h10605 | h10605
                    · rcases h2bigk with h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c | h10606c
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p10393_1, p10606_1]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h4, hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h7821, hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h9029, hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h0, hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h9968, hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h9970, hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h9972, hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        rcases p10606_3 (m.d 0 2) (by simp) with h10617 | h10617
                        · linarith only [h10617, hlam, p10606_0]
                        · rcases p10606_3 (m.d 1 2) (by simp) with h10619 | h10619
                          · linarith only [h10619, h9968, hlam]
                          · rcases p10606_3 (m.d 2 3) (by simp) with h10621 | h10621
                            · rcases p10606_3 (m.d 2 4) (by simp) with h10622 | h10622
                              · linarith only [h10622, h9977, hlam]
                              · linarith only [h10622, h7821, hlam]
                            · linarith only [h10621, hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        rcases p10606_3 (m.d 0 2) (by simp) with h10626 | h10626
                        · linarith only [h10626, h4, hlam]
                        · linarith only [h0, h10626, hlam]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h9029, h9979, hc02, hc23, hlam, hphi, p10393_1, p10606_1]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h0, h9029, hc12, hc23, hlam, hphi, p10393_1, p10606_1]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        rcases p10606_3 (m.d 0 2) (by simp) with h10632 | h10632
                        · linarith only [h10632, hlam, p10606_0]
                        · rcases p10606_3 (m.d 1 2) (by simp) with h10634 | h10634
                          · linarith only [h10634, h9970, hlam]
                          · rcases p10606_3 (m.d 2 3) (by simp) with h10636 | h10636
                            · rcases p10606_3 (m.d 2 4) (by simp) with h10637 | h10637
                              · rcases p10606_3 (m.d 2 5) (by simp) with h10638 | h10638
                                · linarith only [h10638, h9979, hlam]
                                · linarith only [h10638, h9029, hlam]
                              · linarith only [h10637, hlam, p10606_0]
                            · linarith only [h10636, h4, hlam]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        rcases p10606_3 (m.d 0 2) (by simp) with h10643 | h10643
                        · linarith only [h10643, h7821, hlam]
                        · linarith only [h0, h10643, hlam]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h9977, hlam, p10606_1]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h0, h9029, hc12, hc24, hlam, hphi, p10393_1, p10606_1]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        rcases p10606_3 (m.d 0 2) (by simp) with h10649 | h10649
                        · linarith only [h10649, hlam, p10606_0]
                        · rcases p10606_3 (m.d 1 2) (by simp) with h10651 | h10651
                          · linarith only [h10651, h9972, hlam]
                          · rcases p10606_3 (m.d 2 3) (by simp) with h10653 | h10653
                            · rcases p10606_3 (m.d 2 4) (by simp) with h10654 | h10654
                              · rcases p10606_3 (m.d 2 5) (by simp) with h10655 | h10655
                                · rcases h3bigk with h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c | h10656c
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h4, h9974, h9976, h9980, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10656_1]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h4, hlam, p10656_1]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    rcases p10656_3 (m.d 0 3) (by simp) with h10660 | h10660
                                    · rcases p10656_3 (m.d 1 3) (by simp) with h10661 | h10661
                                      · linarith only [h1, h10661, hlam]
                                      · linarith only [h10661, h9974, hlam]
                                    · linarith only [h10660, hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    rcases p10656_3 (m.d 0 3) (by simp) with h10665 | h10665
                                    · rcases p10656_3 (m.d 1 3) (by simp) with h10666 | h10666
                                      · linarith only [h1, h10666, hlam]
                                      · linarith only [h10666, h9975, hlam]
                                    · linarith only [h10665, hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h1, hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h9968, hlam, p10656_1]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    rcases p10656_3 (m.d 0 3) (by simp) with h10673 | h10673
                                    · rcases p10656_3 (m.d 1 3) (by simp) with h10674 | h10674
                                      · rcases p10656_3 (m.d 2 3) (by simp) with h10675 | h10675
                                        · rcases p10656_3 (m.d 3 4) (by simp) with h10676 | h10676
                                          · linarith only [h10676, hlam, p10656_0]
                                          · rcases p10656_3 (m.d 3 5) (by simp) with h10678 | h10678
                                            · linarith only [h10678, h9975, hlam]
                                            · linarith only [h10678, h9980, hlam]
                                        · linarith only [h10675, h9977, hlam]
                                      · linarith only [h10674, hlam, p10656_0]
                                    · linarith only [h10673, h9965, hlam]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    rcases p10656_3 (m.d 0 3) (by simp) with h10684 | h10684
                                    · rcases p10656_3 (m.d 1 3) (by simp) with h10685 | h10685
                                      · rcases p10656_3 (m.d 2 3) (by simp) with h10686 | h10686
                                        · rcases p10656_3 (m.d 3 4) (by simp) with h10687 | h10687
                                          · linarith only [h10687, h9974, hlam]
                                          · rcases p10656_3 (m.d 3 5) (by simp) with h10689 | h10689
                                            · linarith only [h10689, hlam, p10656_0]
                                            · rcases h5bigk with h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c | h10691c
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9976, h9980, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p10691_1]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9029, hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                rcases p10691_3 (m.d 0 5) (by simp) with h10695 | h10695
                                                · rcases p10691_3 (m.d 1 5) (by simp) with h10696 | h10696
                                                  · linarith only [h10696, h3, hlam]
                                                  · linarith only [h10696, h9975, hlam]
                                                · linarith only [h10695, h9966, hlam]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9965, h9967, h9980, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10691_1]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h3, hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9972, hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h3, h9980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10691_1]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9976, h9980, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10691_1]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h0, h9977, h9979, hc12, hc23, hlam, hphi, p10393_1, p10691_1]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9972, h9977, h9979, hc12, hc23, hlam, hphi, p10691_1]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                rcases p10691_3 (m.d 0 5) (by simp) with h10709 | h10709
                                                · linarith only [h10709, h9029, hlam]
                                                · linarith only [h10709, h9966, hlam]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9977, h9979, h9980, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10691_1]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9966, hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9975, hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9978, hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9980, hlam, p10691_1]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9967, hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9976, hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9979, hlam, p10691_0]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [h9980, hc34, hc45, hlam, hphi, p10691_1]
                                              · have p10691_0 := h10691c.1
                                                have p10691_1 := h10691c.2.1
                                                have p10691_2 := h10691c.2.2.1
                                                have p10691_3 := h10691c.2.2.2
                                                linarith only [hlam, p10691_0]
                                        · linarith only [h10686, h9978, hlam]
                                      · linarith only [h10685, hlam, p10656_0]
                                    · linarith only [h10684, h9966, hlam]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h0, h9966, hc12, hc23, hlam, hphi, p10393_1, p10656_1]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h9974, h9976, h9980, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10656_1]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    rcases p10656_3 (m.d 0 3) (by simp) with h10729 | h10729
                                    · linarith only [h10729, h4, hlam]
                                    · linarith only [h10729, h9965, hlam]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    rcases p10656_3 (m.d 0 3) (by simp) with h10732 | h10732
                                    · linarith only [h10732, h4, hlam]
                                    · linarith only [h10732, h9966, hlam]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h9965, hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h9974, hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h9977, hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h9980, hlam, p10656_1]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h9966, hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h9975, hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h9978, hlam, p10656_0]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [h1, h9975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10656_1]
                                  · have p10656_0 := h10656c.1
                                    have p10656_1 := h10656c.2.1
                                    have p10656_2 := h10656c.2.2.1
                                    have p10656_3 := h10656c.2.2.2
                                    linarith only [hlam, p10656_0]
                                · linarith only [h10655, hlam, p10606_0]
                              · linarith only [h10654, h7821, hlam]
                            · linarith only [h10653, h4, hlam]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        rcases p10606_3 (m.d 0 2) (by simp) with h10748 | h10748
                        · linarith only [h10748, h9029, hlam]
                        · linarith only [h0, h10748, hlam]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h9978, hlam, p10606_1]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [h9979, hlam, p10606_0]
                      · have p10606_0 := h10606c.1
                        have p10606_1 := h10606c.2.1
                        have p10606_2 := h10606c.2.2.1
                        have p10606_3 := h10606c.2.2.2
                        linarith only [hlam, p10606_0]
                    · linarith only [h10605, h9029, hlam]
                  · linarith only [h10604, h7821, hlam]
                · linarith only [h10603, h4, hlam]
            · linarith only [h0, h10600, hlam]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h9966, hlam, p10393_0]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [h9967, hlam, p10393_1]
          · have p10393_0 := h10393c.1
            have p10393_1 := h10393c.2.1
            have p10393_2 := h10393c.2.2.1
            have p10393_3 := h10393c.2.2.2
            linarith only [hlam, p10393_0]
      · linarith only [h0, h2, h7821, h9976, h9979, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · linarith only [h4, h9966, h9978, hlam]
  · linarith only [h4, h9965, h9977, hlam]

end R2N4
