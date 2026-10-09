import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAB0_H_I_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h0ehi := hb0.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sAB0_H_I_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_I_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h0ehi := hb0.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_L_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h0elo := hb0.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h4, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h6, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h5, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
            · linarith only [h0, h10, h2, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h10, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · linarith only [h3, hc02, hlam, hphi, ht23, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
          · linarith only [h0, h14, h15, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
            · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
              · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                · linarith only [h0, h17, h19, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h19, hc24, hlam, hphi, u4elo4]
              · linarith only [h0, h17, h18, h2, hc24, hlam, hphi, u4elo3]
            · linarith only [h17, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · linarith only [h14, hc02, hlam, hphi, ht23, ht34, u4elo2]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h26 | h26
    · rcases m.htr 0 2 3 (by decide) (by decide) with h27 | h27
      · rcases m.htr 0 2 4 (by decide) (by decide) with h28 | h28
        · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
            · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
              · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
                · rcases m.htr 3 4 5 (by decide) (by decide) with h33 | h33
                  · linarith only [h27, h31, h33, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h26, h30, h32, h33, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h32, hc24, hlam, hphi, u4elo4]
              · linarith only [h31, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h0, h30, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · linarith only [h0, h27, h29, hlam]
        · linarith only [h28, hc02, hlam, hphi, ht23, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h41 | h41
        · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
          · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
            · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
              · rcases m.htr 2 4 5 (by decide) (by decide) with h45 | h45
                · linarith only [h0, h26, h27, h42, h43, h45, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h45, hc24, hlam, hphi, u4elo4]
              · linarith only [h0, h26, h27, h44, hc14, hlam, hphi, u4elo3]
            · linarith only [h0, h26, h27, h42, h43, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
            · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
              · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                · linarith only [h0, h26, h42, h50, h52, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h52, hc24, hlam, hphi, u4elo4]
              · linarith only [h0, h42, h51, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h26, h50, hc14, hlam, hphi, u4elo2]
        · linarith only [h0, h26, h41, hc14, hlam, hphi, u4elo2]
    · linarith only [h26, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB0_H_L_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5emin := hb5.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
                · rcases h5emin with h8 | h8 | h8 | h8 | h8
                  · linarith only [h1, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                  · linarith only [h0, h4, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                  · linarith only [h0, h2, h4, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                  · linarith only [h0, h2, h4, h6, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                  · linarith only [h0, h4, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                · linarith only [h0, h4, h7, hc24, hlam, hphi, u4elo0]
              · linarith only [h0, h2, h4, h5, h6, hc34, hlam, hphi, u4elo0]
            · linarith only [h5, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h4, hc14, hlam, hphi, u4elo4]
        · linarith only [h3, hc13, hlam, hphi, ht34, u4elo3]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
        · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
          · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
            · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
              · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                · linarith only [h2, h23, hc12, hlam, hphi, ht23, ht34, u4elo2]
                · linarith only [h0, h20, h23, hc24, hlam, hphi, u4elo0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                · linarith only [h21, h22, h26, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h20, h26, hc24, hlam, hphi, u4elo0]
            · linarith only [h21, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h20, hc14, hlam, hphi, u4elo4]
        · linarith only [h19, hc13, hlam, hphi, ht34, u4elo3]
    · linarith only [h1, hc04, hlam, hphi, u4elo4]
  · linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB0_H_L_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h0ehi := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem n7l_sAB0_H_L_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h0elo := hb0.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h4, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h6, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h5, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
            · linarith only [h0, h10, h2, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h10, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · linarith only [h3, hc02, hlam, hphi, ht23, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h14 | h14
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
          · linarith only [h0, h14, h15, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
            · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
              · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                · linarith only [h0, h17, h18, h19, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h19, hc34, hlam, hphi, u4elo4]
              · linarith only [h18, h2, hc02, hlam, hphi, ht23, ht34, u4elo3]
            · linarith only [h17, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · linarith only [h14, hc02, hlam, hphi, ht23, ht34, u4elo2]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h26 | h26
    · rcases m.htr 0 2 3 (by decide) (by decide) with h27 | h27
      · rcases m.htr 0 2 4 (by decide) (by decide) with h28 | h28
        · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
            · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
              · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                · linarith only [h27, h31, h32, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                · linarith only [h32, hc34, hlam, hphi, u4elo4]
              · linarith only [h31, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h0, h30, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · linarith only [h0, h26, h27, h29, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
        · linarith only [h28, hc02, hlam, hphi, ht23, ht34, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h39 | h39
        · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
          · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
            · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
              · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                · linarith only [h0, h26, h27, h40, h41, h42, h43, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h43, hc34, hlam, hphi, u4elo4]
              · linarith only [h0, h27, h42, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h0, h26, h27, h40, h41, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
            · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
              · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                · linarith only [h0, h26, h40, h48, h49, h50, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h50, hc34, hlam, hphi, u4elo4]
              · linarith only [h0, h40, h49, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h0, h26, h48, hc14, hlam, hphi, u4elo2]
        · linarith only [h0, h26, h39, hc14, hlam, hphi, u4elo2]
    · linarith only [h26, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB0_H_L_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h0ehi := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem n7l_sAB0_H_L_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi4]

theorem n7l_sAB0_H_L_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi4]

theorem n7l_sAB0_H_L_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi4]

theorem n7l_sAB0_H_L_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hc34, hlam, hphi, u4elo4]

theorem n7l_sAB0_H_L_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc24 := m.hcor 2 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
  · linarith only [h0, hc24, hlam, hphi, u4elo4]

theorem n7l_sAB0_H_L_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h0ehi := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem n7l_sAB0_H_L_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_L_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_H_L_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h0ehi := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem n7l_sAB0_H_L_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi9]
  · linarith only [h0, hc34, hlam, hphi, u4elo4]

theorem n7l_sAB0_H_L_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.2.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi9]
  · linarith only [h0, hc14, hlam, hphi, u4elo4]

theorem n7l_sAB0_H_L_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h0ehi := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo0]

theorem n7l_sAB0_H_R_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h0elo := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB0_H_R_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
      · linarith only [h1, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
    · linarith only [h1, hc45, hlam, hphi, u4ehi1]
  · linarith only [h0, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB0_H_R_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_H_R_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_H_R_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_H_R_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have h0elo := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB0_H_R_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have h0ehi := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
            · linarith only [h4, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h1, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · linarith only [h8, hc45, hlam, hphi, u4ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
          · linarith only [h11, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
            · linarith only [h0, h13, h2, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h1, h15, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h15, hc45, hlam, hphi, u4ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
        · linarith only [h18, h2, hc12, hlam, hphi, ht01, u0ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
          · linarith only [h0, h2, h20, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
            · linarith only [h0, h2, h22, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
              · linarith only [h1, h24, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h24, hc45, hlam, hphi, u4ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h27 | h27
      · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
        · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
          · linarith only [h0, h1, h29, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
            · linarith only [h0, h1, h29, h31, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
              · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                · linarith only [h0, h1, h28, h29, h34, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · linarith only [h0, h1, h28, h29, h34, hc23, hc34, hlam, hphi]
              · linarith only [h0, h1, h28, h33, hc23, hc45, hlam, hphi, ht34]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
          · linarith only [h27, h28, h38, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
          · linarith only [h0, h1, h27, h28, h38, hc12, hc24, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
        · linarith only [h27, h41, hc12, hlam, hphi, ht01, u0ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
          · linarith only [h0, h43, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
            · linarith only [h0, h1, h43, h45, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
              · rcases m.htr 2 3 4 (by decide) (by decide) with h48 | h48
                · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                    · linarith only [h48, h50, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h50, hc45, hlam, hphi, u4ehi3]
                  · linarith only [h0, h1, h43, h45, h47, h49, hc12, hc25, hlam, hphi]
                · linarith only [h27, h48, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
              · linarith only [h1, h47, hc45, hlam, hphi, u4ehi0]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h56 | h56
    · linarith only [h0, h56, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h58 | h58
      · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
        · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
          · rcases m.htr 1 2 5 (by decide) (by decide) with h61 | h61
            · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
              · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                · linarith only [h58, h63, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h60, h65, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h65, hc45, hlam, hphi, u4ehi2]
              · linarith only [h62, hc45, hlam, hphi, u4ehi1]
            · linarith only [h0, h61, hc25, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h60, hc24, hlam, hphi, ht01, ht12, u0ehi0]
        · linarith only [h0, h59, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
        · linarith only [h58, h72, hc12, hlam, hphi, ht01, u0ehi1]
        · linarith only [h0, h72, hc23, hlam, hphi, ht01, ht12, u0ehi0]

theorem n7l_sAB0_H_R_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h0elo := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB0_H_R_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5emax := hb5.2.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
      · linarith only [h1, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
    · linarith only [h1, hc45, hlam, hphi, u4ehi1]
  · linarith only [h0, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB0_H_R_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h0ehi := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                · linarith only [h1, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h8, hc45, hlam, hphi, u4ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                · linarith only [h1, h11, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h11, hc45, hlam, hphi, u4ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
            · linarith only [h14, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
              · linarith only [h0, h16, h3, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h18 | h18
                · linarith only [h1, h18, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h18, hc45, hlam, hphi, u4ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
          · linarith only [h21, h3, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
            · linarith only [h0, h23, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h25 | h25
              · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                · linarith only [h1, h26, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h26, hc45, hlam, hphi, u4ehi1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                · linarith only [h1, h29, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h29, hc45, hlam, hphi, u4ehi1]
      · linarith only [h1, h2, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h33 | h33
      · rcases m.htr 0 2 3 (by decide) (by decide) with h34 | h34
        · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
          · rcases m.htr 1 2 4 (by decide) (by decide) with h36 | h36
            · linarith only [h0, h36, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
              · linarith only [h0, h1, h36, h38, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                · linarith only [h1, h33, h36, h40, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h1, h33, h35, h38, h40, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
            · linarith only [h34, h35, h43, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · linarith only [h0, h1, h34, h35, h43, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
          · linarith only [h34, h46, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
            · linarith only [h0, h48, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
              · linarith only [h0, h1, h48, h50, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                · linarith only [h1, h33, h48, h52, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h1, h52, hc45, hlam, hphi, u4ehi0]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h55 | h55
        · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
          · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
            · linarith only [h0, h57, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
              · linarith only [h0, h1, h57, h59, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                  · linarith only [h0, h33, h56, h57, h61, h62, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h33, h56, h57, h61, h62, hc23, hc34, hlam, hphi]
                · linarith only [h1, h61, hc45, hlam, hphi, u4ehi0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
            · linarith only [h0, h55, h56, h66, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · linarith only [h0, h1, h55, h56, h66, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h69 | h69
          · linarith only [h55, h69, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
            · linarith only [h0, h1, h71, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h73 | h73
              · linarith only [h0, h1, h71, h73, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h75 | h75
                · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h77 | h77
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h78 | h78
                      · linarith only [h76, h78, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h78, hc45, hlam, hphi, u4ehi3]
                    · linarith only [h71, h75, h77, hlam]
                  · linarith only [h55, h76, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h75, hc45, hlam, hphi, u4ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h84 | h84
    · linarith only [h0, h84, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h86 | h86
      · rcases m.htr 0 2 3 (by decide) (by decide) with h87 | h87
        · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
          · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
            · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
              · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                · linarith only [h84, h86, h89, h91, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h91, hc45, hlam, hphi, u4ehi1]
              · linarith only [h89, h90, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · linarith only [h0, h86, h89, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
          · linarith only [h0, h86, h87, h88, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
          · linarith only [h87, h97, hc12, hlam, hphi, ht01, u0ehi1]
          · linarith only [h0, h86, h97, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h100 | h100
        · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
          · rcases m.htr 1 2 4 (by decide) (by decide) with h102 | h102
            · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
              · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                  · linarith only [h100, h105, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h107 | h107
                    · linarith only [h102, h107, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h104, h107, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h104, hc45, hlam, hphi, u4ehi1]
              · linarith only [h0, h103, hc25, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h102, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h101, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
          · linarith only [h100, h114, hc12, hlam, hphi, ht01, u0ehi1]
          · linarith only [h0, h114, hc23, hlam, hphi, ht01, ht12, u0ehi0]

theorem n7l_sAB0_H_R_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_H_R_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_H_R_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_H_R_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_H_R_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_H_R_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_M_IR_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5emax := hb5.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases h5emax with h0 | h0 | h0 | h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, ht45, u4ehi4]
    · linarith only [h0, h1, hlam, ht45, u4ehi0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
    · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
      · linarith only [h0, h5, hlam, ht45, u4ehi4]
      · linarith only [h0, h5, hlam, ht45, u4ehi1]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
      · linarith only [h0, h4, h8, hlam, ht45, u4ehi0]
      · linarith only [h0, h8, hlam, ht45, u4ehi1]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h11 | h11
    · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
      · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
        · linarith only [h0, h13, hlam, ht45, u4ehi4]
        · linarith only [h0, h13, hlam, ht45, u4ehi2]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
        · linarith only [h0, h12, h16, hlam, ht45, u4ehi1]
        · linarith only [h0, h16, hlam, ht45, u4ehi2]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
      · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
        · linarith only [h0, h11, h20, hlam, ht45, u4ehi0]
        · linarith only [h0, h20, hlam, ht45, u4ehi2]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
        · linarith only [h0, h11, h23, hlam, ht45, u4ehi0]
        · linarith only [h0, h23, hlam, ht45, u4ehi2]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
    · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
      · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
        · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
          · linarith only [h0, h29, hlam, ht45, u4ehi4]
          · linarith only [h0, h29, hlam, ht45, u4ehi3]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
          · linarith only [h0, h28, h32, hlam, ht45, u4ehi2]
          · linarith only [h0, h32, hlam, ht45, u4ehi3]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
        · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
          · linarith only [h0, h27, h36, hlam, ht45, u4ehi1]
          · linarith only [h0, h36, hlam, ht45, u4ehi3]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
          · linarith only [h0, h35, h39, hlam, ht45, u4ehi2]
          · linarith only [h0, h39, hlam, ht45, u4ehi3]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
      · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
        · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
          · linarith only [h0, h26, h44, hlam, ht45, u4ehi0]
          · linarith only [h0, h44, hlam, ht45, u4ehi3]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
          · linarith only [h0, h43, h47, hlam, ht45, u4ehi2]
          · linarith only [h0, h47, hlam, ht45, u4ehi3]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h50 | h50
        · rcases m.htr 3 4 5 (by decide) (by decide) with h51 | h51
          · linarith only [h0, h26, h51, hlam, ht45, u4ehi0]
          · linarith only [h0, h51, hlam, ht45, u4ehi3]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h54 | h54
          · linarith only [h0, h26, h54, hlam, ht45, u4ehi0]
          · linarith only [h0, h54, hlam, ht45, u4ehi3]
  · linarith only [h0, hlam, ht45, u4ehi4]

theorem n7l_sAB0_M_IR_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5emax := hb5.2.2
  have h0ehi := hb0.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h5emax with h0 | h0 | h0 | h0 | h0
  · linarith only [h0, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi4]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
    · linarith only [h0, h2, hlam, ht45, u4ehi4]
    · linarith only [h0, h2, hlam, ht45, u4ehi1]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
    · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
      · linarith only [h0, h6, hlam, ht45, u4ehi4]
      · linarith only [h0, h6, hlam, ht45, u4ehi2]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
      · linarith only [h0, h5, h9, hlam, ht45, u4ehi1]
      · linarith only [h0, h9, hlam, ht45, u4ehi2]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
    · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
      · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht45, u4ehi4]
        · linarith only [h0, h14, hlam, ht45, u4ehi3]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h13, h17, hlam, ht45, u4ehi2]
        · linarith only [h0, h17, hlam, ht45, u4ehi3]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
      · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h12, h21, hlam, ht45, u4ehi1]
        · linarith only [h0, h21, hlam, ht45, u4ehi3]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
        · linarith only [h0, h12, h24, hlam, ht45, u4ehi1]
        · linarith only [h0, h24, hlam, ht45, u4ehi3]
  · linarith only [h0, hlam, ht45, u4ehi4]

theorem n7l_sAB0_M_IR_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_M_IR_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_M_IR_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB0_M_IR_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have h0elo := hb0.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
      · linarith only [h0, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
    · linarith only [h0, h1, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sAB0_M_IR_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hlam, hphi, ht45, u4ehi3, u5elo0]
      · linarith only [h0, h2, hlam, hphi, ht45, u4ehi2, u5elo0]
    · linarith only [h0, h1, hlam, hphi, ht45, u4ehi1, u5elo0]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sAB0_M_IR_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have h0ehi := hb0.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · rcases h5emax with h3 | h3 | h3 | h3 | h3
        · linarith only [h3, hlam, ht01, ht12, ht23, ht34, ht45, u0ehi4]
        · linarith only [h0, h3, hlam, ht45, u4ehi4]
        · linarith only [h1, h3, hlam, ht45, u4ehi4]
        · linarith only [h2, h3, hlam, ht45, u4ehi4]
        · linarith only [h3, hlam, ht45, u4ehi4]
      · linarith only [h0, h2, hlam, hphi, ht45, u4ehi3, u5elo1]
    · linarith only [h0, h1, hlam, hphi, ht45, u4ehi2, u5elo1]
  · linarith only [h0, hlam, hphi, ht45, u4ehi1, u5elo4]

theorem n7l_sAB0_M_LI_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h0ehi := hb0.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi4, u5elo0]

theorem n7l_sAB0_M_LI_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have h0elo := hb0.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi3]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
            · linarith only [h0, h2, h6, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h3, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                · linarith only [h10, h5, h6, h8, hlam]
                · linarith only [h10, h5, h6, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
            · linarith only [h0, h13, h5, hc03, hc34, hlam, hphi]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                · linarith only [h15, h17, h5, hc23, hlam, hphi, ht34, u4elo3]
                · linarith only [h17, h5, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
          · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
            · linarith only [h0, h2, h21, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
              · linarith only [h2, h20, h21, h23, h4, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u4elo2, u5ehi4]
              · linarith only [h2, h20, h23, h4, hc34, hlam, hphi, u4elo4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
            · linarith only [h20, h26, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
              · linarith only [h26, h28, h3, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · linarith only [h20, h28, h3, h4, hc23, hlam, hphi, ht34, u4elo4]
      · linarith only [h2, h3, hc23, hlam, hphi, ht34, u4elo2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
      · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
        · linarith only [h2, h33, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
          · rcases m.htr 2 3 5 (by decide) (by decide) with h36 | h36
            · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
              · linarith only [h37, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
              · linarith only [h32, h33, h37, hc24, hlam, hphi, u4elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
              · linarith only [h32, h40, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · linarith only [h2, h32, h35, h36, h40, hc34, hlam, hphi, u4elo4]
          · linarith only [h2, h35, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h44 | h44
        · linarith only [h2, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
          · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
            · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
              · linarith only [h48, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
              · linarith only [h32, h48, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
              · linarith only [h51, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
              · linarith only [h32, h51, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h2, h46, hc12, hlam, hphi, ht23, ht34, u4elo3]

theorem n7l_sAB0_M_LI_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h3, h4, h6, h8, hlam]
              · linarith only [h3, h4, h8, hc34, hlam, hphi, u4elo4]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
          · linarith only [h11, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
            · linarith only [h13, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h13, h15, h3, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h15, h3, hc23, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
        · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h19, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
            · linarith only [h0, h18, h19, h2, h21, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u4elo2, u5ehi4]
            · linarith only [h0, h18, h2, h21, hc34, hlam, hphi, u4elo4]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
          · linarith only [h18, h24, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
            · linarith only [h1, h26, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · linarith only [h1, h18, h2, h26, hc23, hlam, hphi, ht34, u4elo4]
    · linarith only [h0, h1, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
    · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
      · linarith only [h0, h31, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
        · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
          · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
            · linarith only [h35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h31, h35, hc24, hlam, hphi, u4elo4]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
            · linarith only [h30, h38, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · linarith only [h0, h30, h34, h38, hc24, hlam, hphi, u4elo4]
        · linarith only [h0, h30, h33, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
      · linarith only [h30, h42, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
        · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
          · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
            · linarith only [h46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h46, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
            · linarith only [h49, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h49, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · linarith only [h0, h44, hc12, hlam, hphi, ht23, ht34, u4elo3]

theorem n7l_sAB0_M_LI_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have h0ehi := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0, u5ehi4]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]

theorem n7l_sAB0_M_LI_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_LI_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_LI_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have h0ehi := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · rcases h5bigk with h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo0, u5ehi1]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo0, u5ehi2]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo0, u5ehi3]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo0, u5ehi4]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h1, hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h1, h5, h7, hc01, hlam, hphi, ht0b, ht5b, p8_1, u5ehi4]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h1, h2, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo0, u5ehi4]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo0, u5ehi4]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hc25, hlam, hphi, ht01, ht12, p8_1, u0ehi4]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo2, u5ehi1]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h6, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo2, u5ehi4]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo2, u5ehi4]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p8_1, u0ehi4]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h3, h5, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo2, u5ehi4]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h5, hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h5, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo2, u5ehi4]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h2, hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h3, hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h6, hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [h7, hlam, p8_0]
                  · obtain ⟨p8_0, p8_1, p8_2, p8_3⟩ := h8c
                    linarith only [hlam, p8_0]
                · linarith only [h2, h7, hc34, hlam, hphi, u4elo0]
              · linarith only [h0, h3, h6, hc24, hlam, hphi, u4elo0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
              · linarith only [h36, h4, h5, hlam]
              · linarith only [h0, h3, h36, hc24, hlam, hphi, u4elo0]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
            · linarith only [h39, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi3]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h41 | h41
              · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                · rcases h5bigk with h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c | h43c
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [hlam, p43_0]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p43_1, u4elo0, u5ehi1]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p43_1, u4elo0, u5ehi2]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p43_1, u4elo0, u5ehi3]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p43_1, u4elo0, u5ehi4]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h1, hlam, p43_0]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [hlam, p43_0]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h1, h41, hc01, hlam, hphi, ht0b, ht5b, p43_1, u5ehi4]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h1, h2, h39, hc23, hlam, hphi, ht34, p43_1, u4elo0]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p43_1, u4elo0, u5ehi4]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [hc25, hlam, hphi, ht01, ht12, p43_1, u0ehi4]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h4, h41, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p43_1, u4elo3, u5ehi1]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [hlam, p43_0]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h39, hlam, p43_1]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h4, h41, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p43_1, u4elo3, u5ehi4]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h42, hlam, hphi, ht01, ht12, ht23, ht34, p43_1, u0ehi4, u4elo3]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h3, h42, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p43_1, u4elo3, u5ehi4]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h42, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p43_1, u4elo3, u5ehi2]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [hlam, p43_0]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h42, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p43_1, u4elo3, u5ehi4]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h2, hlam, p43_0]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h3, hlam, p43_0]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h41, hlam, p43_0]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [h42, hlam, p43_0]
                  · obtain ⟨p43_0, p43_1, p43_2, p43_3⟩ := h43c
                    linarith only [hlam, p43_0]
                · linarith only [h2, h4, h42, hc24, hlam, hphi, u4elo0]
              · linarith only [h0, h3, h4, h41, hc23, hlam, hphi, ht34, u4elo0]
        · linarith only [h2, h3, hc14, hlam, hphi, u4elo0]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h73 | h73
      · linarith only [h0, h1, h73, hlam]
      · linarith only [h73, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo4]
  · linarith only [h0, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]

theorem n7l_sAB0_M_LI_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_LI_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h0ehi := hb0.1
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, ht01, ht12, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi4, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_LI_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_LI_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_LI_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h0ehi := hb0.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht01, ht12, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi9]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi3, u4elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n7l_sAB0_M_LR_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB0_M_LR_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB0_M_LR_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB0_M_LR_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB0_M_LR_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB0_M_LR_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB0_M_LR_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have h5ehi := hb5.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB0_M_LR_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have h5ehi := hb5.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi6 := h4ehi (m.d 1 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
  · linarith only [h0, hlam, hphi, u4ehi6, u4elo4]

theorem n7l_sAB0_M_LR_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have h5ehi := hb5.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB0_M_LR_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi6 := h4ehi (m.d 1 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo1]
  · linarith only [h0, hlam, hphi, u4ehi6, u4elo4]

theorem n7l_sAB0_M_LR_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi7 := h4ehi (m.d 2 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo2]
  · linarith only [h0, hlam, hphi, u4ehi7, u4elo4]

theorem n7l_sAB0_M_LR_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi5 := h4ehi (m.d 0 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo0]
  · linarith only [h0, hlam, hphi, u4ehi5, u4elo4]

theorem n7l_sAB0_M_LR_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi6 := h4ehi (m.d 1 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo1]
  · linarith only [h0, hlam, hphi, u4ehi6, u4elo4]

theorem n7l_sAB0_M_LR_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi7 := h4ehi (m.d 2 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo2]
  · linarith only [h0, hlam, hphi, u4ehi7, u4elo4]

theorem n7l_sAB0_M_LR_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB0_M_LR_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB0_M_LR_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB0_M_LR_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

end R2N4
