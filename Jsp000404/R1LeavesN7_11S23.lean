import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S18
import Jsp000404.R1LeavesN7_11S22

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h11650 | h11650
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649 h11650
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649 h11650

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h13893 | h13893
  · rcases m.htr 0 3 4 (by decide) (by decide) with h13894 | h13894
    · linarith only [h11648, h11649, h13894, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h13896 | h13896
      · rcases m.htr 0 4 5 (by decide) (by decide) with h13897 | h13897
        · rcases m.htr 1 2 3 (by decide) (by decide) with h13898 | h13898
          · rcases m.htr 1 2 5 (by decide) (by decide) with h13899 | h13899
            · rcases m.htr 1 3 4 (by decide) (by decide) with h13900 | h13900
              · linarith only [h13894, h13900, hc13, hlam, hphi, ht01, u0ehi2]
              · linarith only [h13900, h8410, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h11649, h13893, h13899, hc12, hc24, hlam, hphi]
          · linarith only [h0, h11648, h11649, h13898, hc24, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h11648, h11649, h13896, h13897, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h13906 | h13906
        · rcases m.htr 1 2 3 (by decide) (by decide) with h13907 | h13907
          · rcases m.htr 1 2 5 (by decide) (by decide) with h13908 | h13908
            · rcases m.htr 1 3 4 (by decide) (by decide) with h13909 | h13909
              · linarith only [h13894, h13907, h13909, hc12, hlam, hphi, ht01, u0ehi2]
              · linarith only [h13909, h8410, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h11649, h13893, h13908, hc12, hc24, hlam, hphi]
          · linarith only [h0, h11648, h11649, h13907, hc24, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h11649, h13893, h13906, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h13915 | h13915
    · linarith only [h11648, h11649, h13915, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h13917 | h13917
      · linarith only [h11648, h13893, h13917, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h13919 | h13919
        · rcases m.htr 1 2 3 (by decide) (by decide) with h13920 | h13920
          · rcases m.htr 1 2 5 (by decide) (by decide) with h13921 | h13921
            · linarith only [h13893, h13921, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h13921, hc25, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h11648, h13920, hc02, hlam, hphi, u0ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h13925 | h13925
          · rcases m.htr 1 2 5 (by decide) (by decide) with h13926 | h13926
            · linarith only [h13893, h13926, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h13926, hc25, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h11648, h11649, h13919, h13925, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h11649 | h11649
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h13930 | h13930
  · rcases m.htr 0 2 5 (by decide) (by decide) with h13931 | h13931
    · rcases m.htr 0 3 4 (by decide) (by decide) with h13932 | h13932
      · rcases m.htr 0 3 5 (by decide) (by decide) with h13933 | h13933
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13934 | h13934
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13935 | h13935
            · linarith only [h11648, h13935, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h13935, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13938 | h13938
            · linarith only [h11648, h13938, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h13938, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h11648, h13931, h13933, hlam]
      · linarith only [h11648, h13930, h13932, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h13943 | h13943
      · rcases m.htr 0 3 5 (by decide) (by decide) with h13944 | h13944
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13945 | h13945
          · linarith only [h13930, h13931, h13945, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13947 | h13947
            · linarith only [h11648, h13947, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h13947, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13950 | h13950
          · linarith only [h11648, h13930, h13944, h13950, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13952 | h13952
            · linarith only [h11648, h13930, h13952, hc12, hlam, hphi, ht01, u0ehi3]
            · linarith only [h0, h13952, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h11648, h13930, h13943, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h13956 | h13956
    · rcases m.htr 0 3 4 (by decide) (by decide) with h13957 | h13957
      · rcases m.htr 0 3 5 (by decide) (by decide) with h13958 | h13958
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13959 | h13959
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13960 | h13960
            · linarith only [h10008, h11648, h13956, h13960, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h13960, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h13930, h13956, h13959, hlam]
        · linarith only [h13930, h13956, h13957, h13958, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h13965 | h13965
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13966 | h13966
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13967 | h13967
            · linarith only [h10008, h11648, h13956, h13967, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h13967, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h11648, h13956, h13957, h13966, hlam]
        · linarith only [h11648, h13956, h13965, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h13972 | h13972
      · rcases m.htr 0 3 5 (by decide) (by decide) with h13973 | h13973
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13974 | h13974
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13975 | h13975
            · linarith only [h0, h11648, h13975, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h13975, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13978 | h13978
            · linarith only [h0, h11648, h13978, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h13978, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13981 | h13981
          · linarith only [h13972, h13973, h13981, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13983 | h13983
            · linarith only [h0, h11648, h13983, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h13983, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h13986 | h13986
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13987 | h13987
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13988 | h13988
            · linarith only [h0, h11648, h13988, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h13988, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h13972, h13986, h13987, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h13992 | h13992
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13993 | h13993
            · linarith only [h0, h11648, h13993, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h13993, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h13996 | h13996
            · linarith only [h0, h11648, h13996, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h13996, hc23, hlam, hphi, ht01, ht12, u0ehi0]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h11648 | h11648
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h10008 | h10008
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008

set_option maxHeartbeats 11178000 in
set_option maxHeartbeats 11178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s9_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h8410 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h8411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h8412 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8413 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8414 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8415 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h8416 | h8416
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8417 | h8417
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8418 | h8418
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8419 | h8419
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8420 | h8420
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8421 | h8421
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8422 | h8422
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8423 | h8423
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8424 | h8424
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8425 | h8425
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8426 | h8426
                      · linarith only [h0, h8410, h8418, h8423, h8426, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h8410, h8420, h8422, h8426, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h8410, h8420, h8422, h8425, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h8410, h8421, h8424, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h8410, h8420, h8423, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8432 | h8432
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8433 | h8433
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8434 | h8434
                    · linarith only [h0, h8410, h8418, h8420, h8422, h8432, h8434, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8436 | h8436
                      · linarith only [h8420, h8422, h8436, hlam]
                      · rcases h2bigk with h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c | h8438c
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h0, hlam, p8438_1]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          rcases p8438_3 (m.d 0 2) (by simp) with h8441 | h8441
                          · rcases p8438_3 (m.d 1 2) (by simp) with h8442 | h8442
                            · rcases p8438_3 (m.d 2 3) (by simp) with h8443 | h8443
                              · linarith only [h8443, hlam, p8438_0]
                              · rcases p8438_3 (m.d 2 4) (by simp) with h8445 | h8445
                                · linarith only [h8413, h8445, hlam]
                                · rcases p8438_3 (m.d 2 5) (by simp) with h8447 | h8447
                                  · linarith only [h8414, h8447, hlam]
                                  · rcases h3bigk with h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c | h8449c
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h0, h8410, h8418, h8433, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8449_1]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h0, h8410, h8433, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8449_1]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      rcases p8449_3 (m.d 0 3) (by simp) with h8453 | h8453
                                      · rcases p8449_3 (m.d 1 3) (by simp) with h8454 | h8454
                                        · linarith only [h8410, h8454, hlam]
                                        · linarith only [h8420, h8454, hlam]
                                      · linarith only [h8453, hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      rcases p8449_3 (m.d 0 3) (by simp) with h8458 | h8458
                                      · rcases p8449_3 (m.d 1 3) (by simp) with h8459 | h8459
                                        · linarith only [h8410, h8459, hlam]
                                        · linarith only [h8421, h8459, hlam]
                                      · linarith only [h8458, hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h8410, hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h0, h8410, h8433, h8436, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8449_1]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h0, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8449_1]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h0, h8410, h8436, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8449_1]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h8412, hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h8418, hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p8438_1, p8449_1]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h0, h8436, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8438_1, p8449_1]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h8415, hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h8420, hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h8432, hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h8436, hlam, p8449_1]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h8416, hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h8421, hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h8433, hlam, p8449_0]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [h0, h8410, h8416, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8449_1]
                                    · have p8449_0 := h8449c.1
                                      have p8449_1 := h8449c.2.1
                                      have p8449_2 := h8449c.2.2.1
                                      have p8449_3 := h8449c.2.2.2
                                      linarith only [hlam, p8449_0]
                            · linarith only [h8418, h8442, hlam]
                          · linarith only [h8441, hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          rcases p8438_3 (m.d 0 2) (by simp) with h8485 | h8485
                          · rcases p8438_3 (m.d 1 2) (by simp) with h8486 | h8486
                            · rcases p8438_3 (m.d 2 3) (by simp) with h8487 | h8487
                              · linarith only [h8412, h8487, hlam]
                              · linarith only [h8432, h8487, hlam]
                            · linarith only [h0, h8410, h8434, h8486, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h8485, hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          rcases p8438_3 (m.d 0 2) (by simp) with h8492 | h8492
                          · rcases p8438_3 (m.d 1 2) (by simp) with h8493 | h8493
                            · rcases p8438_3 (m.d 2 3) (by simp) with h8494 | h8494
                              · linarith only [h8412, h8494, hlam]
                              · linarith only [h8433, h8494, hlam]
                            · linarith only [h8419, h8493, hlam]
                          · linarith only [h8492, hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p8438_1, u0ehi1]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          rcases p8438_3 (m.d 0 2) (by simp) with h8501 | h8501
                          · linarith only [h0, h8501, hlam]
                          · linarith only [h8412, h8501, hlam]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h0, h8410, h8415, h8417, h8434, hlam, p8438_2]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          rcases p8438_3 (m.d 0 2) (by simp) with h8505 | h8505
                          · linarith only [h0, h8505, hlam]
                          · linarith only [h8414, h8505, hlam]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h8412, hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h8418, hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h0, h8410, h8418, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8438_1]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h0, h8410, h8418, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8438_1]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h8413, hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p8438_1]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h8432, hlam, p8438_1]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h8434, hlam, p8438_1]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h8414, hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h8419, hlam, p8438_0]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h8433, hlam, p8438_1]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [h0, h8411, h8419, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8438_1]
                        · have p8438_0 := h8438c.1
                          have p8438_1 := h8438c.2.1
                          have p8438_2 := h8438c.2.2.1
                          have p8438_3 := h8438c.2.2.2
                          linarith only [hlam, p8438_0]
                  · linarith only [h0, h8410, h8421, h8433, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h8410, h8420, h8432, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h0, h8410, h8416, h8420, h8421, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8526 | h8526
            · linarith only [h0, h8410, h8415, h8420, h8526, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8528 | h8528
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8529 | h8529
                · linarith only [h8418, h8420, h8529, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8531 | h8531
                  · linarith only [h8418, h8526, h8531, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8533 | h8533
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8534 | h8534
                      · rcases h2bigk with h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c | h8535c
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h0, hlam, p8535_1]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          rcases p8535_3 (m.d 0 2) (by simp) with h8538 | h8538
                          · rcases p8535_3 (m.d 1 2) (by simp) with h8539 | h8539
                            · rcases p8535_3 (m.d 2 3) (by simp) with h8540 | h8540
                              · linarith only [h8540, hlam, p8535_0]
                              · rcases p8535_3 (m.d 2 4) (by simp) with h8542 | h8542
                                · linarith only [h8413, h8542, hlam]
                                · linarith only [h8529, h8542, hlam]
                            · linarith only [h8418, h8539, hlam]
                          · linarith only [h8538, hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          rcases p8535_3 (m.d 0 2) (by simp) with h8547 | h8547
                          · rcases p8535_3 (m.d 1 2) (by simp) with h8548 | h8548
                            · rcases p8535_3 (m.d 2 3) (by simp) with h8549 | h8549
                              · linarith only [h8412, h8549, hlam]
                              · rcases p8535_3 (m.d 2 4) (by simp) with h8551 | h8551
                                · linarith only [h8551, hlam, p8535_0]
                                · rcases p8535_3 (m.d 2 5) (by simp) with h8553 | h8553
                                  · linarith only [h8414, h8553, hlam]
                                  · rcases h3bigk with h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c | h8555c
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      rcases p8555_3 (m.d 0 3) (by simp) with h8557 | h8557
                                      · rcases p8555_3 (m.d 1 3) (by simp) with h8558 | h8558
                                        · linarith only [h8410, h8558, hlam]
                                        · rcases p8555_3 (m.d 2 3) (by simp) with h8560 | h8560
                                          · linarith only [h8412, h8560, hlam]
                                          · rcases p8555_3 (m.d 3 4) (by simp) with h8562 | h8562
                                            · linarith only [h8415, h8562, hlam]
                                            · linarith only [h8420, h8562, hlam]
                                      · linarith only [h8410, h8557, hlam]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      rcases p8555_3 (m.d 0 3) (by simp) with h8566 | h8566
                                      · rcases p8555_3 (m.d 1 3) (by simp) with h8567 | h8567
                                        · linarith only [h8410, h8567, hlam]
                                        · linarith only [h8418, h8567, hlam]
                                      · linarith only [h8412, h8566, hlam]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h0, h8410, h8526, h8534, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8555_1]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h0, h8410, h8418, h8526, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8555_1]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h8410, hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h8526, h8534, hc23, hc34, hlam, hphi, p8555_1]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h8420, hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h8526, hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h8412, hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h8418, hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h8529, hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h8531, hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h8415, hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h0, h8410, h8415, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8555_1]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h0, h8410, h8415, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8555_1]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h0, h8410, h8415, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8555_1]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h8416, hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h0, h8410, h8416, h8418, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8555_1]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h0, h8410, h8416, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8555_1]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [h8534, hlam, p8555_0]
                                    · have p8555_0 := h8555c.1
                                      have p8555_1 := h8555c.2.1
                                      have p8555_2 := h8555c.2.2.1
                                      have p8555_3 := h8555c.2.2.2
                                      linarith only [hlam, p8555_0]
                            · linarith only [h0, h8410, h8415, h8529, h8548, hlam]
                          · linarith only [h8547, hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          rcases p8535_3 (m.d 0 2) (by simp) with h8595 | h8595
                          · rcases p8535_3 (m.d 1 2) (by simp) with h8596 | h8596
                            · rcases p8535_3 (m.d 2 3) (by simp) with h8597 | h8597
                              · linarith only [h8412, h8597, hlam]
                              · rcases p8535_3 (m.d 2 4) (by simp) with h8599 | h8599
                                · linarith only [h8413, h8599, hlam]
                                · linarith only [h8533, h8599, hlam]
                            · linarith only [h8419, h8596, hlam]
                          · linarith only [h8595, hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p8535_1, u0ehi1]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h0, h8410, h8415, h8418, h8420, hlam, p8535_2]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          rcases p8535_3 (m.d 0 2) (by simp) with h8607 | h8607
                          · linarith only [h0, h8607, hlam]
                          · linarith only [h8413, h8607, hlam]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          rcases p8535_3 (m.d 0 2) (by simp) with h8610 | h8610
                          · linarith only [h0, h8610, hlam]
                          · linarith only [h8414, h8610, hlam]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h8412, hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h8418, hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h8529, hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h8531, hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h8413, hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h0, h8410, h8415, h8529, hlam, p8535_1]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h0, h8410, h8415, h8529, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8535_1]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h0, h8410, h8415, h8529, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8535_1]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h8414, hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h8419, hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h0, h8411, h8419, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8535_1]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [h8533, hlam, p8535_0]
                        · have p8535_0 := h8535c.1
                          have p8535_1 := h8535c.2.1
                          have p8535_2 := h8535c.2.2.1
                          have p8535_3 := h8535c.2.2.2
                          linarith only [hlam, p8535_0]
                      · linarith only [h8420, h8528, h8534, hlam]
                    · linarith only [h0, h8410, h8415, h8420, h8528, h8533, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8630 | h8630
                · linarith only [h8418, h8420, h8630, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8632 | h8632
                  · linarith only [h0, h8410, h8415, h8417, h8418, h8420, h8528, h8632, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8634 | h8634
                    · linarith only [h0, h8410, h8415, h8420, h8528, h8630, h8634, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8636 | h8636
                      · linarith only [h0, h8410, h8415, h8418, h8420, h8528, h8636, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h8410, h8415, h8417, h8418, h8420, h8636, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h8419, hc25, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h8410, h8415, h8417, h8418, hc23, hlam, hphi, ht01, ht12, u0ehi4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8641 | h8641
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8642 | h8642
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8643 | h8643
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8644 | h8644
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8645 | h8645
              · linarith only [h8417, h8645, hc14, hlam, hphi, ht01, u0ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8647 | h8647
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8648 | h8648
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8649 | h8649
                    · linarith only [h8417, h8649, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8651 | h8651
                      · linarith only [h8410, h8417, h8641, h8647, h8651, hc01, hlam, hphi, u0ehi3]
                      · rcases h2bigk with h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c | h8653c
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h0, hlam, p8653_1]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          rcases p8653_3 (m.d 0 2) (by simp) with h8656 | h8656
                          · rcases p8653_3 (m.d 1 2) (by simp) with h8657 | h8657
                            · rcases p8653_3 (m.d 2 3) (by simp) with h8658 | h8658
                              · linarith only [h8658, hlam, p8653_0]
                              · rcases p8653_3 (m.d 2 4) (by simp) with h8660 | h8660
                                · linarith only [h8413, h8660, hlam]
                                · rcases p8653_3 (m.d 2 5) (by simp) with h8662 | h8662
                                  · linarith only [h8414, h8662, hlam]
                                  · rcases h3bigk with h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c | h8664c
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h0, h8410, h8643, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8664_1]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h0, h8410, h8647, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8664_1]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      rcases p8664_3 (m.d 0 3) (by simp) with h8668 | h8668
                                      · rcases p8664_3 (m.d 1 3) (by simp) with h8669 | h8669
                                        · linarith only [h8410, h8669, hlam]
                                        · linarith only [h8643, h8669, hlam]
                                      · linarith only [h8668, hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      rcases p8664_3 (m.d 0 3) (by simp) with h8673 | h8673
                                      · rcases p8664_3 (m.d 1 3) (by simp) with h8674 | h8674
                                        · linarith only [h8410, h8674, hlam]
                                        · linarith only [h8644, h8674, hlam]
                                      · linarith only [h8673, hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h8410, hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h0, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8664_1]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h0, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8664_1]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h0, h8410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8664_1]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h8412, hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h8641, hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8653_1, p8664_1]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8653_1, p8664_1]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h8415, hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h8643, hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h8647, hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h8651, hlam, p8664_1]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h8416, hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h8644, hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h8648, hlam, p8664_0]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [h0, h8410, h8416, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8664_1]
                                    · have p8664_0 := h8664c.1
                                      have p8664_1 := h8664c.2.1
                                      have p8664_2 := h8664c.2.2.1
                                      have p8664_3 := h8664c.2.2.2
                                      linarith only [hlam, p8664_0]
                            · linarith only [h8641, h8657, hlam]
                          · linarith only [h8656, hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          rcases p8653_3 (m.d 0 2) (by simp) with h8700 | h8700
                          · rcases p8653_3 (m.d 1 2) (by simp) with h8701 | h8701
                            · rcases p8653_3 (m.d 2 3) (by simp) with h8702 | h8702
                              · linarith only [h8412, h8702, hlam]
                              · linarith only [h8647, h8702, hlam]
                            · linarith only [h0, h8411, h8642, h8649, h8701, hlam]
                          · linarith only [h8700, hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          rcases p8653_3 (m.d 0 2) (by simp) with h8707 | h8707
                          · rcases p8653_3 (m.d 1 2) (by simp) with h8708 | h8708
                            · rcases p8653_3 (m.d 2 3) (by simp) with h8709 | h8709
                              · linarith only [h8412, h8709, hlam]
                              · linarith only [h8648, h8709, hlam]
                            · linarith only [h8642, h8708, hlam]
                          · linarith only [h8707, hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p8653_1, u0ehi1]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          rcases p8653_3 (m.d 0 2) (by simp) with h8716 | h8716
                          · linarith only [h0, h8716, hlam]
                          · linarith only [h8412, h8716, hlam]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          rcases p8653_3 (m.d 0 2) (by simp) with h8719 | h8719
                          · linarith only [h0, h8719, hlam]
                          · linarith only [h8413, h8719, hlam]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          rcases p8653_3 (m.d 0 2) (by simp) with h8722 | h8722
                          · linarith only [h0, h8722, hlam]
                          · linarith only [h8414, h8722, hlam]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h8412, hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h8641, hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h0, h8410, h8641, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8653_1]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h0, h8410, h8641, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8653_1]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h8413, hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p8653_1]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h8647, hlam, p8653_1]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h8649, hlam, p8653_1]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h8414, hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h8642, hlam, p8653_0]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h8648, hlam, p8653_1]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [h0, h8411, h8642, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8653_1]
                        · have p8653_0 := h8653c.1
                          have p8653_1 := h8653c.2.1
                          have p8653_2 := h8653c.2.2.1
                          have p8653_3 := h8653c.2.2.2
                          linarith only [hlam, p8653_0]
                  · linarith only [h0, h8410, h8644, h8648, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h8410, h8643, h8647, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h0, h8410, h8416, h8643, h8644, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8743 | h8743
            · linarith only [h0, h8410, h8415, h8643, h8743, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8745 | h8745
              · linarith only [h8417, h8745, hc14, hlam, hphi, ht01, u0ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8747 | h8747
                · linarith only [h8641, h8643, h8747, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8749 | h8749
                  · linarith only [h0, h8410, h8415, h8641, h8643, h8743, h8745, h8749, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8751 | h8751
                    · linarith only [h8417, h8751, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8753 | h8753
                      · linarith only [h0, h8410, h8415, h8417, h8753, hc12, hlam, hphi, ht01, u0ehi3]
                      · rcases h2bigk with h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c | h8755c
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h0, hlam, p8755_1]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          rcases p8755_3 (m.d 0 2) (by simp) with h8758 | h8758
                          · rcases p8755_3 (m.d 1 2) (by simp) with h8759 | h8759
                            · rcases p8755_3 (m.d 2 3) (by simp) with h8760 | h8760
                              · linarith only [h8760, hlam, p8755_0]
                              · rcases p8755_3 (m.d 2 4) (by simp) with h8762 | h8762
                                · linarith only [h8413, h8762, hlam]
                                · linarith only [h8747, h8762, hlam]
                            · linarith only [h8641, h8759, hlam]
                          · linarith only [h8758, hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          rcases p8755_3 (m.d 0 2) (by simp) with h8767 | h8767
                          · rcases p8755_3 (m.d 1 2) (by simp) with h8768 | h8768
                            · rcases p8755_3 (m.d 2 3) (by simp) with h8769 | h8769
                              · linarith only [h8412, h8769, hlam]
                              · rcases p8755_3 (m.d 2 4) (by simp) with h8771 | h8771
                                · linarith only [h8771, hlam, p8755_0]
                                · rcases p8755_3 (m.d 2 5) (by simp) with h8773 | h8773
                                  · linarith only [h8414, h8773, hlam]
                                  · linarith only [h8751, h8773, hlam]
                            · linarith only [h0, h8411, h8642, h8751, h8768, hlam]
                          · linarith only [h8767, hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          rcases p8755_3 (m.d 0 2) (by simp) with h8778 | h8778
                          · rcases p8755_3 (m.d 1 2) (by simp) with h8779 | h8779
                            · rcases p8755_3 (m.d 2 3) (by simp) with h8780 | h8780
                              · linarith only [h8412, h8780, hlam]
                              · rcases p8755_3 (m.d 2 4) (by simp) with h8782 | h8782
                                · linarith only [h8413, h8782, hlam]
                                · rcases p8755_3 (m.d 2 5) (by simp) with h8784 | h8784
                                  · linarith only [h8784, hlam, p8755_0]
                                  · rcases h3bigk with h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c | h8786c
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      rcases p8786_3 (m.d 0 3) (by simp) with h8788 | h8788
                                      · rcases p8786_3 (m.d 1 3) (by simp) with h8789 | h8789
                                        · linarith only [h8410, h8789, hlam]
                                        · rcases p8786_3 (m.d 2 3) (by simp) with h8791 | h8791
                                          · linarith only [h8412, h8791, hlam]
                                          · rcases p8786_3 (m.d 3 4) (by simp) with h8793 | h8793
                                            · linarith only [h8415, h8793, hlam]
                                            · linarith only [h8643, h8793, hlam]
                                      · linarith only [h8410, h8788, hlam]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      rcases p8786_3 (m.d 0 3) (by simp) with h8797 | h8797
                                      · rcases p8786_3 (m.d 1 3) (by simp) with h8798 | h8798
                                        · linarith only [h8410, h8798, hlam]
                                        · linarith only [h8641, h8798, hlam]
                                      · linarith only [h8412, h8797, hlam]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h0, h8410, h8641, h8643, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8786_1]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h0, h8410, h8641, h8743, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8786_1]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h8410, hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h8643, hc23, hc34, hlam, hphi, p8786_1]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h8643, hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h8743, hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h8412, hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h8641, hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h8747, hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h8749, hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h8415, hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h0, h8410, h8415, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8786_1]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h0, h8410, h8415, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8786_1]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h8753, hlam, p8786_1]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h8416, hlam, p8786_0]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h0, h8410, h8416, h8641, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8786_1]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h0, h8410, h8416, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8786_1]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [h0, h8410, h8416, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8786_1]
                                    · have p8786_0 := h8786c.1
                                      have p8786_1 := h8786c.2.1
                                      have p8786_2 := h8786c.2.2.1
                                      have p8786_3 := h8786c.2.2.2
                                      linarith only [hlam, p8786_0]
                            · linarith only [h8642, h8779, hlam]
                          · linarith only [h8778, hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p8755_1, u0ehi1]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h0, h8410, h8415, h8641, h8643, hlam, p8755_2]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          rcases p8755_3 (m.d 0 2) (by simp) with h8829 | h8829
                          · linarith only [h0, h8829, hlam]
                          · linarith only [h8413, h8829, hlam]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          rcases p8755_3 (m.d 0 2) (by simp) with h8832 | h8832
                          · linarith only [h0, h8832, hlam]
                          · linarith only [h8414, h8832, hlam]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h8412, hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h8641, hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h8747, hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h8749, hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h8413, hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h0, h8410, h8416, h8642, h8743, h8751, hlam, p8755_1]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h0, h8410, h8416, h8642, h8743, h8751, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8755_1]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h8751, hlam, p8755_1]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h8414, hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h8642, hlam, p8755_0]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h0, h8410, h8416, h8642, h8743, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8755_1]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [h0, h8410, h8416, h8642, h8743, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8755_1]
                        · have p8755_0 := h8755c.1
                          have p8755_1 := h8755c.2.1
                          have p8755_2 := h8755c.2.2.1
                          have p8755_3 := h8755c.2.2.2
                          linarith only [hlam, p8755_0]
        · linarith only [h0, h8642, hc25, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h8410, h8416, h8417, h8641, hc23, hlam, hphi, ht01, ht12, u0ehi3]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8852 | h8852
    · linarith only [h8415, h8416, h8852, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8854 | h8854
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8855 | h8855
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8856 | h8856
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8857 | h8857
            · linarith only [h8416, h8857, hc13, hlam, hphi, ht01, u0ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8859 | h8859
              · linarith only [h8852, h8859, hc14, hlam, hphi, ht01, u0ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8861 | h8861
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8862 | h8862
                  · linarith only [h8411, h8415, h8416, h8854, h8857, h8862, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h8864 | h8864
                    · linarith only [h8852, h8864, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h8866 | h8866
                      · linarith only [h8852, h8866, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · rcases h2bigk with h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h0, hlam, p8868_1]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          rcases p8868_3 (m.d 0 2) (by simp) with h8871 | h8871
                          · rcases p8868_3 (m.d 1 2) (by simp) with h8872 | h8872
                            · rcases p8868_3 (m.d 2 3) (by simp) with h8873 | h8873
                              · linarith only [h8873, hlam, p8868_0]
                              · rcases p8868_3 (m.d 2 4) (by simp) with h8875 | h8875
                                · linarith only [h8413, h8875, hlam]
                                · rcases p8868_3 (m.d 2 5) (by simp) with h8877 | h8877
                                  · linarith only [h8414, h8877, hlam]
                                  · linarith only [h8862, h8877, hlam]
                            · linarith only [h8854, h8872, hlam]
                          · linarith only [h8871, hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          rcases p8868_3 (m.d 0 2) (by simp) with h8882 | h8882
                          · rcases p8868_3 (m.d 1 2) (by simp) with h8883 | h8883
                            · rcases p8868_3 (m.d 2 3) (by simp) with h8884 | h8884
                              · linarith only [h8412, h8884, hlam]
                              · linarith only [h8861, h8884, hlam]
                            · linarith only [h0, h8411, h8854, h8857, h8861, h8883, hlam]
                          · linarith only [h8882, hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          rcases p8868_3 (m.d 0 2) (by simp) with h8889 | h8889
                          · rcases p8868_3 (m.d 1 2) (by simp) with h8890 | h8890
                            · rcases p8868_3 (m.d 2 3) (by simp) with h8891 | h8891
                              · linarith only [h8412, h8891, hlam]
                              · rcases p8868_3 (m.d 2 4) (by simp) with h8893 | h8893
                                · linarith only [h8413, h8893, hlam]
                                · rcases p8868_3 (m.d 2 5) (by simp) with h8895 | h8895
                                  · linarith only [h8895, hlam, p8868_0]
                                  · rcases h3bigk with h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c | h8897c
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8416, h8866, hc13, hc45, hlam, hphi, ht34, p8897_1]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8416, h8861, h8866, hc34, hc45, hlam, hphi, p8897_1]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8416, h8866, hc34, hc45, hlam, hphi, p8897_1]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8416, hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8410, hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h0, h8410, h8415, h8416, h8861, h8866, hc12, hc34, hc45, hlam, hphi, ht01, p8897_1, u0ehi3]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h0, h8410, h8415, h8416, h8866, hc12, hc34, hc45, hlam, hphi, ht01, p8897_1, u0ehi3]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8857, hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8412, hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8854, hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8412, h8416, h8866, hc34, hc45, hlam, hphi, p8897_1]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8862, hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8415, hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8856, hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8861, hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [hlam, p8897_0]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8866, hlam, p8897_1]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8415, h8866, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p8897_1, u0ehi3]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8856, h8866, hc34, hc45, hlam, hphi, p8897_1]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [h8861, h8866, hc34, hc45, hlam, hphi, p8897_1]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      rcases p8897_3 (m.d 0 3) (by simp) with h8921 | h8921
                                      · linarith only [h8416, h8921, hlam]
                                      · linarith only [h8415, h8921, hlam]
                                    · have p8897_0 := h8897c.1
                                      have p8897_1 := h8897c.2.1
                                      have p8897_2 := h8897c.2.2.1
                                      have p8897_3 := h8897c.2.2.2
                                      linarith only [hlam, p8897_0]
                            · linarith only [h8855, h8890, hlam]
                          · linarith only [h8889, hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p8868_1, u0ehi1]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          rcases p8868_3 (m.d 0 2) (by simp) with h8929 | h8929
                          · linarith only [h0, h8929, hlam]
                          · linarith only [h8412, h8929, hlam]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          rcases p8868_3 (m.d 0 2) (by simp) with h8932 | h8932
                          · linarith only [h0, h8932, hlam]
                          · linarith only [h8413, h8932, hlam]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          rcases p8868_3 (m.d 0 2) (by simp) with h8935 | h8935
                          · linarith only [h0, h8935, hlam]
                          · linarith only [h8414, h8935, hlam]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h8412, hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h8854, hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h0, h8410, h8854, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8868_1]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h8862, hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h8413, hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p8868_1]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h8861, hlam, p8868_1]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h8864, hlam, p8868_1]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h8414, hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h8855, hlam, p8868_0]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h8411, h8855, h8861, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8868_1]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [h0, h8411, h8415, h8416, h8855, h8866, hc12, hc24, hc45, hlam, hphi, ht01, p8868_1, u0ehi3]
                        · have p8868_0 := h8868c.1
                          have p8868_1 := h8868c.2.1
                          have p8868_2 := h8868c.2.2.1
                          have p8868_3 := h8868c.2.2.2
                          linarith only [hlam, p8868_0]
                · linarith only [h8415, h8416, h8861, hc23, hc35, hlam, hphi]
          · linarith only [h8415, h8416, h8854, h8856, hc23, hc35, hlam, hphi]
        · linarith only [h0, h8855, hc25, hlam, hphi, ht01, ht12, u0ehi0]
      · linarith only [h0, h8854, hc23, hlam, hphi, ht01, ht12, u0ehi0]

end R2N4
