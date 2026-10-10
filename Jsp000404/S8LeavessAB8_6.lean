import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n8l_sAB8_H_I_M_LI (m : N8Model)
    (hb5 : CMSig2_8_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc06 := m.hcor 0 6 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have h6elo := hb6.1
  have h6bigk := hb6.2.2.2
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  rcases h6bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc16, hlam, hphi, p0_1, u6elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc26, hlam, hphi, p0_1, u6elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc36, hlam, hphi, p0_1, u6elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc46, hlam, hphi, p0_1, u6elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc56, hlam, hphi, p0_1, u6elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc06, hlam, hphi, p0_1, u6elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc26, hlam, hphi, p0_1, u6elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc36, hlam, hphi, p0_1, u6elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc46, hlam, hphi, p0_1, u6elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc56, hlam, hphi, p0_1, u6elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc06, hlam, hphi, p0_1, u6elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc16, hlam, hphi, p0_1, u6elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc36, hlam, hphi, p0_1, u6elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc46, hlam, hphi, p0_1, u6elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc56, hlam, hphi, p0_1, u6elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc06, hlam, hphi, p0_1, u6elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc16, hlam, hphi, p0_1, u6elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc26, hlam, hphi, p0_1, u6elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc46, hlam, hphi, p0_1, u6elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc56, hlam, hphi, p0_1, u6elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc06, hlam, hphi, p0_1, u6elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc16, hlam, hphi, p0_1, u6elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc26, hlam, hphi, p0_1, u6elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc36, hlam, hphi, p0_1, u6elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc56, hlam, hphi, p0_1, u6elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc06, hlam, hphi, p0_1, u6elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc16, hlam, hphi, p0_1, u6elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc26, hlam, hphi, p0_1, u6elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc36, hlam, hphi, p0_1, u6elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc46, hlam, hphi, p0_1, u6elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n8l_sAB8_H_L_H_R (m : N8Model)
    (hb5 : CMSig2_8_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_R m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h6ehi := hb6.1
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u5elo5, u6ehi5]

theorem n8l_sAB8_H_L_M_IR (m : N8Model)
    (hb5 : CMSig2_8_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h6ehi := hb6.2.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases m.htr 4 5 6 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u5elo4, u6ehi5]
  · linarith only [h0, hc45, hlam, hphi, u5elo5]

theorem n8l_sAB8_H_L_M_LI (m : N8Model)
    (hb5 : CMSig2_8_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc06 := m.hcor 0 6 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h6elo := hb6.1
  have h6bigk := hb6.2.2.2
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  rcases h6bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc16, hlam, hphi, p0_1, u6elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc26, hlam, hphi, p0_1, u6elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc36, hlam, hphi, p0_1, u6elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc46, hlam, hphi, p0_1, u6elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc56, hlam, hphi, p0_1, u6elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc06, hlam, hphi, p0_1, u6elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc26, hlam, hphi, p0_1, u6elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc36, hlam, hphi, p0_1, u6elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc46, hlam, hphi, p0_1, u6elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc56, hlam, hphi, p0_1, u6elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc06, hlam, hphi, p0_1, u6elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc16, hlam, hphi, p0_1, u6elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc36, hlam, hphi, p0_1, u6elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc46, hlam, hphi, p0_1, u6elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc56, hlam, hphi, p0_1, u6elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc06, hlam, hphi, p0_1, u6elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc16, hlam, hphi, p0_1, u6elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc26, hlam, hphi, p0_1, u6elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc46, hlam, hphi, p0_1, u6elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc56, hlam, hphi, p0_1, u6elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc06, hlam, hphi, p0_1, u6elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc16, hlam, hphi, p0_1, u6elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc26, hlam, hphi, p0_1, u6elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc36, hlam, hphi, p0_1, u6elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc56, hlam, hphi, p0_1, u6elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc06, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc16, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc26, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n8l_sAB8_H_L_M_LR (m : N8Model)
    (hb5 : CMSig2_8_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_LR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h6ehi := hb6.2.2.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u6ehi11 := h6ehi (m.d 5 6) (by simp)
  rcases m.htr 4 5 6 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u5elo4, u6ehi11]
  · linarith only [h0, hc45, hlam, hphi, u5elo5]

theorem n8l_sAB8_H_R_H_I (m : N8Model)
    (hb5 : CMSig2_8_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_I m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc05 := m.hcor 0 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5ehi := hb5.1
  have h6emax := hb6.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 5 6) (by simp)
  rcases m.htr 0 5 6 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 5 6 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 5 6 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 5 6 (by decide) (by decide) with h3 | h3
        · rcases m.htr 4 5 6 (by decide) (by decide) with h4 | h4
          · rcases h6emax with h5 | h5 | h5 | h5 | h5 | h5
            · linarith only [h0, h5, hlam, ht56, u5ehi5]
            · linarith only [h1, h5, hlam, ht56, u5ehi5]
            · linarith only [h2, h5, hlam, ht56, u5ehi5]
            · linarith only [h3, h5, hlam, ht56, u5ehi5]
            · linarith only [h4, h5, hlam, ht56, u5ehi5]
            · linarith only [h5, hlam, ht56, u5ehi5]
          · linarith only [h0, h4, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi4]
        · linarith only [h2, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b, u5ehi3]
      · linarith only [h2, hc56, hlam, hphi, u5ehi2]
    · linarith only [h0, h1, hc05, hlam, hphi, ht0b, ht56, ht6b, u5ehi1]
  · linarith only [h0, hc56, hlam, hphi, u5ehi0]

theorem n8l_sAB8_H_R_H_L (m : N8Model)
    (hb5 : CMSig2_8_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5ehi := hb5.1
  have h6elo := hb6.1
  have u5ehi5 := h5ehi (m.d 5 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  linarith only [hlam, hphi, ht56, u5ehi5, u6elo5]

theorem n8l_sAB8_H_R_M_LI (m : N8Model)
    (hb5 : CMSig2_8_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5ehi := hb5.1
  have h6elo := hb6.1
  have u5ehi5 := h5ehi (m.d 5 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  linarith only [hlam, hphi, ht56, u5ehi5, u6elo5]

theorem n8l_sAB8_H_R_M_LR (m : N8Model)
    (hb5 : CMSig2_8_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_LR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5ehi := hb5.1
  have h6elo := hb6.1
  have u5ehi5 := h5ehi (m.d 5 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  linarith only [hlam, hphi, ht56, u5ehi5, u6elo5]

theorem n8l_sAB8_M_IR_H_L (m : N8Model)
    (hb5 : CMSig2_8_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5ehi := hb5.2.1
  have h6elo := hb6.1
  have u5ehi5 := h5ehi (m.d 5 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  linarith only [hlam, hphi, ht56, u5ehi5, u6elo5]

theorem n8l_sAB8_M_IR_M_LI (m : N8Model)
    (hb5 : CMSig2_8_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5ehi := hb5.2.1
  have h6elo := hb6.1
  have h6emax := hb6.2.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 5 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  rcases m.htr 0 5 6 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 5 6 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 5 6 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 5 6 (by decide) (by decide) with h3 | h3
        · rcases m.htr 4 5 6 (by decide) (by decide) with h4 | h4
          · rcases h6emax with h5 | h5 | h5 | h5 | h5 | h5
            · linarith only [h0, h5, hlam, ht56, u5ehi5]
            · linarith only [h1, h5, hlam, ht56, u5ehi5]
            · linarith only [h2, h5, hlam, ht56, u5ehi5]
            · linarith only [h3, h5, hlam, ht56, u5ehi5]
            · linarith only [h4, h5, hlam, ht56, u5ehi5]
            · linarith only [h5, hlam, ht56, u5ehi5]
          · linarith only [h0, h4, hlam, hphi, ht56, u5ehi4, u6elo0]
        · linarith only [h0, h3, hlam, hphi, ht56, u5ehi3, u6elo0]
      · linarith only [h0, h2, hlam, hphi, ht56, u5ehi2, u6elo0]
    · linarith only [h0, h1, hlam, hphi, ht56, u5ehi1, u6elo0]
  · linarith only [h0, hlam, hphi, ht56, u5ehi0, u6elo5]

theorem n8l_sAB8_M_LI_H_R (m : N8Model)
    (hb5 : CMSig2_8_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_R m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h6ehi := hb6.1
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 6 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 6 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi4]
          · rcases m.htr 3 5 6 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u5elo2, u6ehi5]
            · rcases m.htr 4 5 6 (by decide) (by decide) with h8 | h8
              · linarith only [h3, h4, h6, h8, hlam]
              · linarith only [h3, h4, h8, hc45, hlam, hphi, u5elo5]
        · rcases m.htr 3 4 6 (by decide) (by decide) with h11 | h11
          · linarith only [h11, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi4]
          · rcases m.htr 3 5 6 (by decide) (by decide) with h13 | h13
            · linarith only [h13, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u5elo3, u6ehi5]
            · rcases m.htr 4 5 6 (by decide) (by decide) with h15 | h15
              · linarith only [h13, h15, h3, hc34, hlam, hphi, ht45, u5elo4]
              · linarith only [h15, h3, hc34, hlam, hphi, ht45, u5elo5]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
        · rcases m.htr 3 4 6 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h19, h2, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi4]
          · rcases m.htr 3 5 6 (by decide) (by decide) with h21 | h21
            · linarith only [h0, h18, h19, h2, h21, hc45, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u5elo3, u6ehi5]
            · linarith only [h0, h18, h2, h21, hc45, hlam, hphi, u5elo5]
        · rcases m.htr 3 4 6 (by decide) (by decide) with h24 | h24
          · linarith only [h18, h24, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u5elo3, u6ehi4]
          · rcases m.htr 3 5 6 (by decide) (by decide) with h26 | h26
            · linarith only [h1, h26, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi5]
            · linarith only [h0, h2, h26, hc34, hlam, hphi, ht45, u5elo5]
    · linarith only [h0, h1, hc34, hlam, hphi, ht45, u5elo3]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
    · rcases m.htr 2 3 6 (by decide) (by decide) with h31 | h31
      · linarith only [h0, h31, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h33 | h33
        · rcases m.htr 3 4 6 (by decide) (by decide) with h34 | h34
          · rcases m.htr 3 5 6 (by decide) (by decide) with h35 | h35
            · linarith only [h35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u5elo3, u6ehi5]
            · linarith only [h30, h31, h35, hc35, hlam, hphi, u5elo5]
          · rcases m.htr 3 5 6 (by decide) (by decide) with h38 | h38
            · linarith only [h30, h38, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi5]
            · linarith only [h0, h30, h34, h38, hc35, hlam, hphi, u5elo5]
        · linarith only [h0, h30, h33, hc35, hlam, hphi, u5elo4]
    · rcases m.htr 2 3 6 (by decide) (by decide) with h42 | h42
      · linarith only [h30, h42, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
        · rcases m.htr 3 4 6 (by decide) (by decide) with h45 | h45
          · rcases m.htr 3 5 6 (by decide) (by decide) with h46 | h46
            · linarith only [h46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u5elo3, u6ehi5]
            · linarith only [h30, h46, hc23, hlam, hphi, ht34, ht45, u5elo5]
          · rcases m.htr 3 5 6 (by decide) (by decide) with h49 | h49
            · linarith only [h49, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u5elo3, u6ehi5]
            · linarith only [h30, h49, hc23, hlam, hphi, ht34, ht45, u5elo5]
        · linarith only [h0, h44, hc23, hlam, hphi, ht34, ht45, u5elo4]

theorem n8l_sAB8_M_LI_M_IR (m : N8Model)
    (hb5 : CMSig2_8_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h6ehi := hb6.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo0, u6ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo1, u6ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo2, u6ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo3, u6ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo4, u6ehi5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n8l_sAB8_M_LI_M_LR (m : N8Model)
    (hb5 : CMSig2_8_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_LR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h6elo := hb6.1
  have h6ehi := hb6.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  have u6ehi11 := h6ehi (m.d 5 6) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo0, u6ehi11]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo1, u6ehi11]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo2, u6ehi11]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo3, u6ehi11]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, p0_1, u5elo4, u6ehi11]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht56, p0_1, u6elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht56, p0_1, u6elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht56, p0_1, u6elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht56, p0_1, u6elo5]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n8l_sAB8_M_LR_H_I (m : N8Model)
    (hb5 : CMSig2_8_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_I m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u5ehi10 := h5ehi (m.d 4 5) (by simp)
  have u5ehi11 := h5ehi (m.d 5 6) (by simp)
  rcases m.htr 4 5 6 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u5ehi11, u5elo4]
  · linarith only [h0, hlam, hphi, u5ehi10, u5elo5]

theorem n8l_sAB8_M_LR_H_L (m : N8Model)
    (hb5 : CMSig2_8_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h5ehi := hb5.2.2.1
  have h6elo := hb6.1
  have u5ehi11 := h5ehi (m.d 5 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  linarith only [hlam, hphi, ht56, u5ehi11, u6elo5]

theorem n8l_sAB8_M_LR_H_R (m : N8Model)
    (hb5 : CMSig2_8_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_H_R m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h6ehi := hb6.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u5ehi10 := h5ehi (m.d 4 5) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases m.htr 4 5 6 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u5elo4, u6ehi5]
  · linarith only [h0, hlam, hphi, u5ehi10, u5elo5]

theorem n8l_sAB8_M_LR_M_IR (m : N8Model)
    (hb5 : CMSig2_8_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u5ehi9 := h5ehi (m.d 3 5) (by simp)
  have u5ehi11 := h5ehi (m.d 5 6) (by simp)
  rcases m.htr 3 5 6 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u5ehi11, u5elo3]
  · linarith only [h0, hlam, hphi, u5ehi9, u5elo5]

theorem n8l_sAB8_M_LR_M_LI (m : N8Model)
    (hb5 : CMSig2_8_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u5ehi8 := h5ehi (m.d 2 5) (by simp)
  have u5ehi11 := h5ehi (m.d 5 6) (by simp)
  rcases m.htr 2 5 6 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u5ehi11, u5elo2]
  · linarith only [h0, hlam, hphi, u5ehi8, u5elo5]

theorem n8l_sAB8_M_LR_M_LR (m : N8Model)
    (hb5 : CMSig2_8_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5) (m.d 5 6))
    (hb6 : CMSig2_8_M_LR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5elo5 := h5elo (m.d 5 6) (by simp)
  have u5ehi10 := h5ehi (m.d 4 5) (by simp)
  have u5ehi11 := h5ehi (m.d 5 6) (by simp)
  rcases m.htr 4 5 6 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u5ehi11, u5elo4]
  · linarith only [h0, hlam, hphi, u5ehi10, u5elo5]

end R2N4
