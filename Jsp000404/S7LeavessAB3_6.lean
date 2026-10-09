import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAB3_H_I_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h3ehi := hb3.1
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  linarith only [hlam, hphi, ht34, ht45, u3ehi4, u5elo3]

theorem n7l_sAB3_H_L_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h3ehi := hb3.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  linarith only [hlam, hphi, ht34, u3ehi3, u4elo3]

theorem n7l_sAB3_H_L_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h3ehi := hb3.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  linarith only [hlam, hphi, ht34, u3ehi3, u4elo3]

theorem n7l_sAB3_H_L_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_H_L_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_H_L_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_H_L_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h3ehi := hb3.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  linarith only [hlam, hphi, ht34, u3ehi3, u4elo3]

theorem n7l_sAB3_H_L_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h3ehi := hb3.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  linarith only [hlam, hphi, ht34, u3ehi3, u4elo3]

theorem n7l_sAB3_H_L_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h3ehi := hb3.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  linarith only [hlam, hphi, ht34, u3ehi3, u4elo3]

theorem n7l_sAB3_H_R_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_H_R_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_H_R_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_H_R_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_H_R_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_H_R_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_H_R_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_H_R_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_H_R_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_M_IR_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_M_IR_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_M_IR_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB3_M_LI_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h3ehi := hb3.1
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  linarith only [hlam, hphi, ht34, ht45, u3ehi4, u5elo3]

theorem n7l_sAB3_M_LR_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB3_M_LR_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB3_M_LR_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB3_M_LR_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_M_LR_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_M_LR_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_M_LR_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_M_LR_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_M_LR_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_M_LR_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_M_LR_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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

theorem n7l_sAB3_M_LR_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
