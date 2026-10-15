import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S24
import Jsp000404.R1LeavesN7_0S34
import Jsp000404.R1LeavesN7_0S35

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11350000 in
set_option maxHeartbeats 11350000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h13284

set_option maxHeartbeats 11350000 in
set_option maxHeartbeats 11350000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 3 5 (by decide) (by decide) with h13284 | h13284
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h13284
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h13284

set_option maxHeartbeats 37904000 in
set_option maxHeartbeats 37904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s7 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7

set_option maxHeartbeats 38368000 in
set_option maxHeartbeats 38368000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s6 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h18959 | h18959
    · rcases m.htr 0 3 5 (by decide) (by decide) with h18960 | h18960
      · linarith only [h18960, h4, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h18962 | h18962
        · linarith only [h18959, h18962, h4, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h18964 | h18964
          · rcases m.htr 1 2 4 (by decide) (by decide) with h18965 | h18965
            · rcases m.htr 1 2 5 (by decide) (by decide) with h18966 | h18966
              · linarith only [h0, h18959, h18966, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h18968 | h18968
                · rcases m.htr 1 3 5 (by decide) (by decide) with h18969 | h18969
                  · linarith only [h1, h18960, h18969, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h18971 | h18971
                    · linarith only [h18962, h18971, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h18973 | h18973
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h18974 | h18974
                        · linarith only [h0, h18960, h18964, h18974, h6, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h18976 | h18976
                          · linarith only [h0, h18962, h18964, h18965, h18973, h18976, h2, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h18964, h18973, h18976, h6, hc34, hc45, hlam, hphi]
                      · linarith only [h18959, h18960, h18973, hc23, hc35, hlam, hphi]
                · linarith only [h18959, h18960, h18968, hc13, hc35, hlam, hphi]
            · linarith only [h18965, h5, h6, hc12, hc25, hlam, hphi]
          · linarith only [h18964, h4, h6, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h18983 | h18983
      · linarith only [h18983, h4, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h18985 | h18985
        · linarith only [h18985, h5, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h18987 | h18987
          · rcases m.htr 1 2 4 (by decide) (by decide) with h18988 | h18988
            · rcases m.htr 1 2 5 (by decide) (by decide) with h18989 | h18989
              · linarith only [h0, h18989, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h18991 | h18991
                · linarith only [h1, h18959, h18991, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h18993 | h18993
                  · linarith only [h1, h18983, h18993, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h18995 | h18995
                    · linarith only [h18985, h18995, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h18997 | h18997
                      · linarith only [h0, h1, h18959, h18987, h18997, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h18999 | h18999
                        · linarith only [h18983, h18999, h4, h6, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h19001 | h19001
                          · linarith only [h0, h1, h18959, h18985, h18988, h19001, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h19003 | h19003
                            · linarith only [h19001, h19003, h4, h6, hc23, hc34, hlam, hphi]
                            · rcases h1bigk with h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c | h19005c
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                rcases p19005_3 (m.d 0 1) (by simp) with h19007 | h19007
                                · rcases p19005_3 (m.d 1 2) (by simp) with h19008 | h19008
                                  · linarith only [h19008, hlam, p19005_0]
                                  · rcases p19005_3 (m.d 1 3) (by simp) with h19010 | h19010
                                    · linarith only [h1, h19010, hlam]
                                    · rcases p19005_3 (m.d 1 4) (by simp) with h19012 | h19012
                                      · linarith only [h19012, h2, hlam]
                                      · rcases p19005_3 (m.d 1 5) (by simp) with h19014 | h19014
                                        · linarith only [h19014, h3, hlam]
                                        · linarith only [h18989, h19014, hlam]
                                · linarith only [h19007, hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                rcases p19005_3 (m.d 0 1) (by simp) with h19018 | h19018
                                · rcases p19005_3 (m.d 1 2) (by simp) with h19019 | h19019
                                  · linarith only [h0, h19019, hlam]
                                  · linarith only [h18987, h19019, hlam]
                                · linarith only [h19018, hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                rcases p19005_3 (m.d 0 1) (by simp) with h19023 | h19023
                                · rcases p19005_3 (m.d 1 2) (by simp) with h19024 | h19024
                                  · linarith only [h0, h19024, hlam]
                                  · linarith only [h18988, h19024, hlam]
                                · linarith only [h19023, hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                rcases p19005_3 (m.d 0 1) (by simp) with h19028 | h19028
                                · rcases p19005_3 (m.d 1 2) (by simp) with h19029 | h19029
                                  · linarith only [h0, h19029, hlam]
                                  · rcases p19005_3 (m.d 1 3) (by simp) with h19031 | h19031
                                    · linarith only [h1, h19031, hlam]
                                    · rcases p19005_3 (m.d 1 4) (by simp) with h19033 | h19033
                                      · linarith only [h19033, h2, hlam]
                                      · rcases p19005_3 (m.d 1 5) (by simp) with h19035 | h19035
                                        · linarith only [h19035, hlam, p19005_0]
                                        · rcases h1emax with h19037 | h19037 | h19037 | h19037 | h19037
                                          · linarith only [h18988, h18989, h18997, h19037, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19005_1]
                                          · rcases h2bigk with h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c | h19039c
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [hlam, p19039_0]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18988, h18997, h6, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p19039_1]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19039_1]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18997, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19039_1]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h6, hlam, p19039_0]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h0, hlam, p19039_1]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [hlam, p19039_0]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18989, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19005_1, p19039_1]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18989, h18997, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19005_1, p19039_1]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18989, hlam, p19039_0]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h4, hlam, p19039_0]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18987, hlam, p19039_0]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [hlam, p19039_0]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18997, hlam, p19039_1]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18999, hlam, p19039_1]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h5, hlam, p19039_0]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18988, hlam, p19039_0]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18999, h19003, h5, h6, hc23, hc45, hlam, hphi, ht34, p19039_1]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [hlam, p19039_0]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h19001, hlam, p19039_0]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18999, h19003, h4, hc23, hc45, hlam, hphi, ht34, p19039_1]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [h18987, h18999, h19003, hc23, hc45, hlam, hphi, ht34, p19039_1]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              rcases p19039_3 (m.d 0 2) (by simp) with h19062 | h19062
                                              · linarith only [h19062, h6, hlam]
                                              · linarith only [h19062, h4, hlam]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              rcases p19039_3 (m.d 0 2) (by simp) with h19065 | h19065
                                              · linarith only [h19065, h6, hlam]
                                              · linarith only [h19065, h5, hlam]
                                            · have p19039_0 := h19039c.1
                                              have p19039_1 := h19039c.2.1
                                              have p19039_2 := h19039c.2.2.1
                                              have p19039_3 := h19039c.2.2.2
                                              linarith only [hlam, p19039_0]
                                          · rcases h2bigk with h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c | h19069c
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [hlam, p19069_0]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h18988, h18997, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19069_1]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19069_1]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h18997, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19069_1]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h6, hlam, p19069_0]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h0, hlam, p19069_1]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [hlam, p19069_0]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h0, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19069_1]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h0, h18997, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19069_1]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h18989, hlam, p19069_0]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h4, hlam, p19069_0]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h18987, hlam, p19069_0]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [hlam, p19069_0]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h18997, hlam, p19069_1]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h18999, hlam, p19069_1]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h5, hlam, p19069_0]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h18988, hlam, p19069_0]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h18999, h19003, h5, h6, hc23, hc45, hlam, hphi, ht34, p19069_1]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [hlam, p19069_0]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h19001, hlam, p19069_0]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h18999, h19003, h4, hc23, hc45, hlam, hphi, ht34, p19069_1]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [h18987, h18999, h19003, hc23, hc45, hlam, hphi, ht34, p19069_1]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              rcases p19069_3 (m.d 0 2) (by simp) with h19092 | h19092
                                              · linarith only [h19092, h6, hlam]
                                              · linarith only [h19092, h4, hlam]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              rcases p19069_3 (m.d 0 2) (by simp) with h19095 | h19095
                                              · linarith only [h19095, h6, hlam]
                                              · linarith only [h19095, h5, hlam]
                                            · have p19069_0 := h19069c.1
                                              have p19069_1 := h19069c.2.1
                                              have p19069_2 := h19069c.2.2.1
                                              have p19069_3 := h19069c.2.2.2
                                              linarith only [hlam, p19069_0]
                                          · rcases h2bigk with h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c | h19099c
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [hlam, p19099_0]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h18988, h18997, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19099_1]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19099_1]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h18997, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19099_1]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h6, hlam, p19099_0]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h0, hlam, p19099_1]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [hlam, p19099_0]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h0, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19099_1]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h0, h18997, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19099_1]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h18989, hlam, p19099_0]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h4, hlam, p19099_0]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h18987, hlam, p19099_0]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [hlam, p19099_0]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h18997, hlam, p19099_1]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h18999, hlam, p19099_1]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h5, hlam, p19099_0]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h18988, hlam, p19099_0]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h18999, h19003, h5, h6, hc23, hc45, hlam, hphi, ht34, p19099_1]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [hlam, p19099_0]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h19001, hlam, p19099_0]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h18999, h19003, h4, hc23, hc45, hlam, hphi, ht34, p19099_1]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [h18987, h18999, h19003, hc23, hc45, hlam, hphi, ht34, p19099_1]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              rcases p19099_3 (m.d 0 2) (by simp) with h19122 | h19122
                                              · linarith only [h19122, h6, hlam]
                                              · linarith only [h19122, h4, hlam]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              rcases p19099_3 (m.d 0 2) (by simp) with h19125 | h19125
                                              · linarith only [h19125, h6, hlam]
                                              · linarith only [h19125, h5, hlam]
                                            · have p19099_0 := h19099c.1
                                              have p19099_1 := h19099c.2.1
                                              have p19099_2 := h19099c.2.2.1
                                              have p19099_3 := h19099c.2.2.2
                                              linarith only [hlam, p19099_0]
                                          · rcases h2bigk with h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c | h19129c
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [hlam, p19129_0]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h18988, h18997, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19129_1]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19129_1]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h18997, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19129_1]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h6, hlam, p19129_0]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h0, hlam, p19129_1]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [hlam, p19129_0]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h0, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19129_1]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h0, h18997, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19129_1]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h18989, hlam, p19129_0]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h4, hlam, p19129_0]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h18987, hlam, p19129_0]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [hlam, p19129_0]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h18997, hlam, p19129_1]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h18999, hlam, p19129_1]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h5, hlam, p19129_0]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h18988, hlam, p19129_0]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h18999, h19003, h5, h6, hc23, hc45, hlam, hphi, ht34, p19129_1]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [hlam, p19129_0]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h19001, hlam, p19129_0]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h18999, h19003, h4, hc23, hc45, hlam, hphi, ht34, p19129_1]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [h18987, h18999, h19003, hc23, hc45, hlam, hphi, ht34, p19129_1]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              rcases p19129_3 (m.d 0 2) (by simp) with h19152 | h19152
                                              · linarith only [h19152, h6, hlam]
                                              · linarith only [h19152, h4, hlam]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              rcases p19129_3 (m.d 0 2) (by simp) with h19155 | h19155
                                              · linarith only [h19155, h6, hlam]
                                              · linarith only [h19155, h5, hlam]
                                            · have p19129_0 := h19129c.1
                                              have p19129_1 := h19129c.2.1
                                              have p19129_2 := h19129c.2.2.1
                                              have p19129_3 := h19129c.2.2.2
                                              linarith only [hlam, p19129_0]
                                · linarith only [h19028, hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h0, hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h0, h18987, h18999, h19003, h6, hc23, hc45, hlam, hphi, ht34, p19005_1]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h0, h18999, h19003, h6, hc14, hc45, hlam, hphi, p19005_1]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h18989, hlam, p19005_1]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h1, hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h18987, hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h18991, hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h18993, hlam, p19005_1]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h2, hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h18988, hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h18987, h18999, h19003, h2, h5, h6, hc23, hc45, hlam, hphi, ht34, p19005_1]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h18995, hlam, p19005_1]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h3, hlam, p19005_0]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [h18987, h18999, h19003, h3, h6, hc23, hc45, hlam, hphi, ht34, p19005_1]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                rcases p19005_3 (m.d 0 1) (by simp) with h19177 | h19177
                                · rcases p19005_3 (m.d 1 2) (by simp) with h19178 | h19178
                                  · linarith only [h18989, h19178, hlam]
                                  · linarith only [h18987, h19178, hlam]
                                · linarith only [h1, h19177, hlam]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                rcases p19005_3 (m.d 0 1) (by simp) with h19182 | h19182
                                · rcases p19005_3 (m.d 1 2) (by simp) with h19183 | h19183
                                  · linarith only [h18989, h19183, hlam]
                                  · linarith only [h18988, h19183, hlam]
                                · linarith only [h19182, h2, hlam]
                              · have p19005_0 := h19005c.1
                                have p19005_1 := h19005c.2.1
                                have p19005_2 := h19005c.2.2.1
                                have p19005_3 := h19005c.2.2.2
                                linarith only [hlam, p19005_0]
            · linarith only [h18988, h5, h6, hc12, hc25, hlam, hphi]
          · linarith only [h18987, h4, h6, hc12, hc25, hlam, hphi]

end R2N4
