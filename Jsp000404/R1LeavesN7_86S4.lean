import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_14_25_L_0_M_LI (m : N7Model)
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases h5bigk with h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c | h2c
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc15, hlam, hphi, p2_1, u5elo0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc25, hlam, hphi, p2_1, u5elo0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc35, hlam, hphi, p2_1, u5elo0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc45, hlam, hphi, p2_1, u5elo0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc25, hlam, hphi, p2_1, u5elo1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hc35, hlam, hphi, p2_1, u5elo0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hc45, hlam, hphi, p2_1, u5elo0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h1, hlam, p2_1]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc15, hlam, hphi, p2_1, u5elo2]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h1, hc35, hlam, hphi, p2_1, u5elo0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h1, hc45, hlam, hphi, p2_1, u5elo0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc05, hlam, hphi, p2_1, u5elo3]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc15, hlam, hphi, p2_1, u5elo3]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc25, hlam, hphi, p2_1, u5elo3]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc45, hlam, hphi, p2_1, u5elo3]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [h0, hc15, hlam, hphi, p2_1, u5elo4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc15, hlam, hphi, p2_1, u5elo4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc25, hlam, hphi, p2_1, u5elo4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hc35, hlam, hphi, p2_1, u5elo4]
      · have p2_0 := h2c.1
        have p2_1 := h2c.2.1
        have p2_2 := h2c.2.2.1
        have p2_3 := h2c.2.2.2
        linarith only [hlam, p2_0]
    · rcases h5bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hlam, p28_0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc15, hlam, hphi, p28_1, u5elo0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hlam, p28_0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc35, hlam, hphi, p28_1, u5elo2]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc45, hlam, hphi, p28_1, u5elo2]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h0, hlam, p28_0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hlam, p28_0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc05, hlam, hphi, p28_1, u5elo1]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc35, hlam, hphi, p28_1, u5elo1]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h0, hc45, hlam, hphi, p28_1, u5elo0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc05, hlam, hphi, p28_1, u5elo2]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc15, hlam, hphi, p28_1, u5elo2]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hlam, p28_0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc35, hlam, hphi, p28_1, u5elo2]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc45, hlam, hphi, p28_1, u5elo2]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p28_1, u5elo3]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc15, hlam, hphi, p28_1, u5elo3]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc25, hlam, hphi, p28_1, u5elo3]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hlam, p28_0]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc45, hlam, hphi, p28_1, u5elo3]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc02, hlam, hphi, ht23, ht34, p28_1, u4elo4]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc15, hlam, hphi, p28_1, u5elo4]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [h1, hc02, hlam, hphi, ht23, ht34, ht45, p28_1, u5elo4]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hc35, hlam, hphi, p28_1, u5elo4]
      · have p28_0 := h28c.1
        have p28_1 := h28c.2.1
        have p28_2 := h28c.2.2.1
        have p28_3 := h28c.2.2.2
        linarith only [hlam, p28_0]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h54 | h54
    · rcases h5bigk with h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c | h55c
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hlam, p55_0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hlam, p55_1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc25, hlam, hphi, p55_1, u5elo0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hc35, hlam, hphi, p55_1, u5elo1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hc45, hlam, hphi, p55_1, u5elo1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc05, hlam, hphi, p55_1, u5elo1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hlam, p55_0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc25, hlam, hphi, p55_1, u5elo1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc35, hlam, hphi, p55_1, u5elo1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc45, hlam, hphi, p55_1, u5elo1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h54, hlam, p55_1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc15, hlam, hphi, p55_1, u5elo2]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hlam, p55_0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h54, hc35, hlam, hphi, p55_1, u5elo0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, h54, hc45, hlam, hphi, p55_1, u5elo1]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc05, hlam, hphi, p55_1, u5elo3]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p55_1, u5elo3]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc25, hlam, hphi, p55_1, u5elo3]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hlam, p55_0]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc45, hlam, hphi, p55_1, u5elo3]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, p55_1, u4elo4]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p55_1, u5elo4]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc25, hlam, hphi, p55_1, u5elo4]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hc35, hlam, hphi, p55_1, u5elo4]
      · have p55_0 := h55c.1
        have p55_1 := h55c.2.1
        have p55_2 := h55c.2.2.1
        have p55_3 := h55c.2.2.2
        linarith only [hlam, p55_0]
    · rcases h5bigk with h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hlam, p81_0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hlam, p81_1]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h54, hlam, p81_0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc35, hlam, hphi, p81_1, u5elo0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc45, hlam, hphi, p81_1, u5elo1]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc05, hlam, hphi, p81_1, u5elo1]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hlam, p81_0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h54, hc02, hlam, hphi, ht23, ht34, ht45, p81_1, u5elo1]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc35, hlam, hphi, p81_1, u5elo1]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc45, hlam, hphi, p81_1, u5elo1]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p81_1, u5elo2]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc15, hlam, hphi, p81_1, u5elo2]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hlam, p81_0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc35, hlam, hphi, p81_1, u5elo2]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc45, hlam, hphi, p81_1, u5elo2]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p81_1, u5elo3]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p81_1, u5elo3]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc25, hlam, hphi, p81_1, u5elo3]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hlam, p81_0]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc45, hlam, hphi, p81_1, u5elo3]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, p81_1, u4elo4]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p81_1, u5elo4]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [h54, hc02, hlam, hphi, ht23, ht34, ht45, p81_1, u5elo4]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hc35, hlam, hphi, p81_1, u5elo4]
      · have p81_0 := h81c.1
        have p81_1 := h81c.2.1
        have p81_2 := h81c.2.2.1
        have p81_3 := h81c.2.2.2
        linarith only [hlam, p81_0]

theorem r1l7_14_25_L_R_H_I (m : N7Model)
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
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
        · rcases h5emax with h10 | h10 | h10 | h10 | h10
          · linarith only [h0, h10, h3, hlam, ht45, u4ehi3]
          · linarith only [h1, h10, h3, hlam, ht45, u4ehi3]
          · linarith only [h10, h2, h3, hlam, ht45, u4ehi3]
          · linarith only [h10, h3, hlam, ht45, u4ehi3]
          · linarith only [h10, h3, hlam, ht45, u4ehi3]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
        · rcases h5emax with h17 | h17 | h17 | h17 | h17
          · linarith only [h0, h17, h2, hlam, ht45, u4ehi2]
          · linarith only [h1, h17, h2, hlam, ht45, u4ehi2]
          · linarith only [h17, h2, hlam, ht45, u4ehi2]
          · linarith only [h16, h17, h2, hlam, ht45, u4ehi2]
          · linarith only [h17, h2, hlam, ht45, u4ehi2]
        · rcases h5emax with h23 | h23 | h23 | h23 | h23
          · linarith only [h0, h2, h23, hlam, ht45, u4ehi2]
          · linarith only [h1, h2, h23, hlam, ht45, u4ehi2]
          · linarith only [h2, h23, hlam, ht45, u4ehi2]
          · linarith only [h16, h23, hlam, ht45, u4ehi3]
          · linarith only [h2, h23, hlam, ht45, u4ehi2]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h29 | h29
      · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
        · rcases h5emax with h31 | h31 | h31 | h31 | h31
          · linarith only [h0, h1, h31, hlam, ht45, u4ehi1]
          · linarith only [h1, h31, hlam, ht45, u4ehi1]
          · linarith only [h1, h29, h31, hlam, ht45, u4ehi1]
          · linarith only [h1, h30, h31, hlam, ht45, u4ehi1]
          · linarith only [h1, h31, hlam, ht45, u4ehi1]
        · rcases h5emax with h37 | h37 | h37 | h37 | h37
          · linarith only [h0, h1, h37, hlam, ht45, u4ehi1]
          · linarith only [h1, h37, hlam, ht45, u4ehi1]
          · linarith only [h1, h29, h37, hlam, ht45, u4ehi1]
          · linarith only [h30, h37, hlam, ht45, u4ehi3]
          · linarith only [h1, h37, hlam, ht45, u4ehi1]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
        · rcases h5emax with h44 | h44 | h44 | h44 | h44
          · linarith only [h0, h1, h44, hlam, ht45, u4ehi1]
          · linarith only [h1, h44, hlam, ht45, u4ehi1]
          · linarith only [h29, h44, hlam, ht45, u4ehi2]
          · linarith only [h1, h43, h44, hlam, ht45, u4ehi1]
          · linarith only [h1, h44, hlam, ht45, u4ehi1]
        · rcases h5emax with h50 | h50 | h50 | h50 | h50
          · linarith only [h0, h1, h50, hlam, ht45, u4ehi1]
          · linarith only [h1, h50, hlam, ht45, u4ehi1]
          · linarith only [h29, h50, hlam, ht45, u4ehi2]
          · linarith only [h43, h50, hlam, ht45, u4ehi3]
          · linarith only [h1, h50, hlam, ht45, u4ehi1]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
    · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
      · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
        · rcases h5emax with h59 | h59 | h59 | h59 | h59
          · linarith only [h0, h59, hlam, ht45, u4ehi0]
          · linarith only [h0, h56, h59, hlam, ht45, u4ehi0]
          · linarith only [h0, h57, h59, hlam, ht45, u4ehi0]
          · linarith only [h0, h58, h59, hlam, ht45, u4ehi0]
          · linarith only [h0, h59, hlam, ht45, u4ehi0]
        · rcases h5emax with h65 | h65 | h65 | h65 | h65
          · linarith only [h0, h65, hlam, ht45, u4ehi0]
          · linarith only [h0, h56, h65, hlam, ht45, u4ehi0]
          · linarith only [h0, h57, h65, hlam, ht45, u4ehi0]
          · linarith only [h58, h65, hlam, ht45, u4ehi3]
          · linarith only [h0, h65, hlam, ht45, u4ehi0]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
        · rcases h5emax with h72 | h72 | h72 | h72 | h72
          · linarith only [h0, h72, hlam, ht45, u4ehi0]
          · linarith only [h0, h56, h72, hlam, ht45, u4ehi0]
          · linarith only [h57, h72, hlam, ht45, u4ehi2]
          · linarith only [h0, h71, h72, hlam, ht45, u4ehi0]
          · linarith only [h0, h72, hlam, ht45, u4ehi0]
        · rcases h5emax with h78 | h78 | h78 | h78 | h78
          · linarith only [h0, h78, hlam, ht45, u4ehi0]
          · linarith only [h0, h56, h78, hlam, ht45, u4ehi0]
          · linarith only [h57, h78, hlam, ht45, u4ehi2]
          · linarith only [h71, h78, hlam, ht45, u4ehi3]
          · linarith only [h0, h78, hlam, ht45, u4ehi0]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h84 | h84
      · rcases m.htr 3 4 5 (by decide) (by decide) with h85 | h85
        · rcases h5emax with h86 | h86 | h86 | h86 | h86
          · linarith only [h0, h86, hlam, ht45, u4ehi0]
          · linarith only [h56, h86, hlam, ht45, u4ehi1]
          · linarith only [h0, h84, h86, hlam, ht45, u4ehi0]
          · linarith only [h0, h85, h86, hlam, ht45, u4ehi0]
          · linarith only [h0, h86, hlam, ht45, u4ehi0]
        · rcases h5emax with h92 | h92 | h92 | h92 | h92
          · linarith only [h0, h92, hlam, ht45, u4ehi0]
          · linarith only [h56, h92, hlam, ht45, u4ehi1]
          · linarith only [h0, h84, h92, hlam, ht45, u4ehi0]
          · linarith only [h85, h92, hlam, ht45, u4ehi3]
          · linarith only [h0, h92, hlam, ht45, u4ehi0]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
        · rcases h5emax with h99 | h99 | h99 | h99 | h99
          · linarith only [h0, h99, hlam, ht45, u4ehi0]
          · linarith only [h56, h99, hlam, ht45, u4ehi1]
          · linarith only [h84, h99, hlam, ht45, u4ehi2]
          · linarith only [h0, h98, h99, hlam, ht45, u4ehi0]
          · linarith only [h0, h99, hlam, ht45, u4ehi0]
        · rcases h5emax with h105 | h105 | h105 | h105 | h105
          · linarith only [h0, h105, hlam, ht45, u4ehi0]
          · linarith only [h105, h56, hlam, ht45, u4ehi1]
          · linarith only [h105, h84, hlam, ht45, u4ehi2]
          · linarith only [h105, h98, hlam, ht45, u4ehi3]
          · linarith only [h0, h105, hlam, ht45, u4ehi0]

theorem r1l7_20_11_13_14_H_I_L_R_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h10, hlam, hphi, ht34, u3ehi2, u4elo3]
                    · linarith only [h8, h9, hlam, hphi, ht34, u3ehi1, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h14, h15, h3, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h15, h8, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h14, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
                · linarith only [h2, h7, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h5, h6, hc35, hlam, hphi, u3ehi3]
            · linarith only [h5, hlam, hphi, ht34, u3ehi0, u4elo3]
          · linarith only [h0, h4, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h23 | h23
          · rcases m.htr 0 3 4 (by decide) (by decide) with h24 | h24
            · rcases m.htr 0 3 5 (by decide) (by decide) with h25 | h25
              · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                  · linarith only [h2, h23, h27, h3, hc12, hlam, hphi, u1ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                        · rcases h0bigk with h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c | h32c
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [hlam, p32_0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h0, h29, h30, h31, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p32_1, u3ehi4]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h1, h27, h29, h30, h31, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p32_1, u3ehi4]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h0, h2, h29, h3, h30, h31, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p32_1, u1ehi3, u3ehi4]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h25, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p32_1, u3ehi4]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h0, hlam, p32_0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [hlam, p32_0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h3, hlam, p32_0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h2, h3, hc23, hlam, hphi, ht12, p32_1, u1ehi3]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h25, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p32_1, u3ehi4]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h1, hlam, p32_1]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h0, h29, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p32_1]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [hlam, p32_0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h2, h3, hc23, hlam, hphi, ht12, p32_1, u1ehi3]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h25, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p32_1, u3ehi4]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h2, hlam, p32_0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h23, hlam, p32_0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h24, hlam, p32_0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [hlam, p32_0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h23, h25, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p32_1, u3ehi4]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p32_1, u1ehi0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h0, h26, h29, h30, h31, hlam, hphi, ht34, p32_1, u3ehi4, u4elo0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h25, hlam, p32_0]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [h26, hlam, p32_1]
                          · have p32_0 := h32c.1
                            have p32_1 := h32c.2.1
                            have p32_2 := h32c.2.2.1
                            have p32_3 := h32c.2.2.2
                            linarith only [hlam, p32_0]
                        · linarith only [h31, hlam, hphi, ht34, u3ehi3, u4elo4]
                      · linarith only [h0, h3, h30, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h29, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
                · linarith only [h2, h26, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · linarith only [h24, h25, hc35, hlam, hphi, u3ehi3]
            · linarith only [h24, hlam, hphi, ht34, u3ehi0, u4elo3]
          · linarith only [h0, h23, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h67 | h67
    · linarith only [h0, h67, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h69 | h69
      · linarith only [h0, h69, hc12, hlam, hphi, u1ehi3]
      · linarith only [h69, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem r1l7_20_11_13_14_H_R_L_R_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0ehi := hb0.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h12, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                    · linarith only [h16, h7, hc23, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h18, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h15, h18, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                    · linarith only [h21, h4, h7, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                      · linarith only [h15, h23, hc24, hlam, hphi, ht12, u1ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                        · linarith only [h15, h25, h7, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                        · linarith only [h25, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · linarith only [h0, h3, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                · linarith only [h30, h4, h5, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                    · linarith only [h30, h33, hc23, hlam, hphi, ht12, u1ehi2]
                    · linarith only [h33, h4, h5, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h32, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h29, h3, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
            · linarith only [h0, h2, h38, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
              · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h0, h2, h38, h40, h43, h44, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h38, h40, h42, h44, hc14, hlam, hphi, u1ehi4]
                    · linarith only [h4, h40, h43, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                  · linarith only [h38, h40, h42, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                    · linarith only [h0, h2, h41, h50, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h4, h50, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h38, h40, h49, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h54 | h54
                · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                        · linarith only [h1, h54, h58, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h2, h38, h55, h56, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h38, h55, h57, hlam]
                    · linarith only [h4, h56, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                      · linarith only [h55, h63, h64, hc23, hlam, hphi, ht12, u1ehi3]
                      · linarith only [h38, h64, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h1, h54, h63, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                    · linarith only [h0, h2, h54, h69, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h4, h69, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h72 | h72
                    · linarith only [h4, h54, h72, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h4, h72, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h3, hc25, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_11_13_14_M_LR_L_0_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h12, h6, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h12, h3, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                          · linarith only [h0, h15, h6, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h15, h3, hc23, hlam, hphi, u3elo0]
                      · linarith only [h10, h4, hc13, hlam, hphi, u3elo0]
                    · linarith only [h3, h6, h9, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                      · linarith only [h21, h6, h8, hlam]
                      · linarith only [h21, h4, hc13, hlam, hphi, u3elo0]
                    · linarith only [h20, h3, h6, hc23, hlam, hphi, u3elo0]
                · linarith only [h0, h2, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                · linarith only [h0, h1, h26, h6, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
                  · linarith only [h0, h1, h28, h6, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                                · linarith only [h0, h1, h30, h36, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                                · linarith only [h0, h1, h26, h32, h33, h36, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h26, h32, h35, hlam]
                            · linarith only [h31, h34, h6, hlam]
                          · linarith only [h3, h33, h6, hc13, hlam, hphi, u3elo0]
                        · linarith only [h26, h3, h32, h5, hc12, hlam, hphi, ht23, u3elo0]
                      · linarith only [h30, h31, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · linarith only [h3, h30, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
              · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
                · rcases m.htr 1 2 5 (by decide) (by decide) with h47 | h47
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                        · linarith only [h5, h50, hlam, hphi, ht01, u0ehi8, u1elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                          · linarith only [h0, h45, h52, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · linarith only [h48, h52, hc23, hlam, hphi, u3elo1]
                      · linarith only [h4, h49, hc13, hlam, hphi, u3elo0]
                    · linarith only [h3, h45, h48, hc23, hlam, hphi, u3elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                      · linarith only [h45, h47, h58, hlam]
                      · linarith only [h4, h58, hc13, hlam, hphi, u3elo0]
                    · linarith only [h3, h45, h57, hc23, hlam, hphi, u3elo0]
                · linarith only [h0, h2, h45, h46, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
                · linarith only [h0, h1, h45, h63, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h0, h1, h45, h65, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h69 | h69
                        · linarith only [h5, h69, hlam, hphi, ht01, u0ehi8, u1elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h72 | h72
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h73 | h73
                              · linarith only [h0, h1, h5, h71, h73, hlam, hphi, ht01, u0ehi8, u1elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h75 | h75
                                · linarith only [h5, h67, h75, hlam, hphi, ht01, u0ehi8, u1elo2]
                                · rcases h4bigk with h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c | h77c
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [hlam, p77_0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h5, hc14, hc45, hlam, hphi, p77_1]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h5, h63, hc12, hc45, hlam, hphi, ht23, ht34, p77_1]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h5, hc34, hc45, hlam, hphi, p77_1]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h5, hlam, p77_0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [hlam, hphi, ht01, p77_1, u0ehi8, u1elo3]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [hlam, p77_0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h63, hlam, p77_0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h0, h1, h63, h72, h73, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p77_1, u1elo0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h69, hlam, p77_0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h2, hlam, p77_1]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h0, h1, h72, h73, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p77_1, u1elo0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [hlam, p77_0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h0, h1, h72, h73, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p77_1, u1elo0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h73, hlam, p77_0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h3, hlam, p77_1]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h67, hlam, p77_0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h71, hlam, p77_0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [hlam, p77_0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h75, hlam, p77_0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h0, h1, h63, h72, h73, hc12, hc45, hlam, hphi, ht01, ht23, ht34, p77_1, u0ehi8, u1elo0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    rcases p77_3 (m.d 0 4) (by simp) with h99 | h99
                                    · linarith only [h5, h99, hlam]
                                    · linarith only [h0, h1, h63, h72, h73, h99, hlam, hphi, ht01, u0ehi8, u1elo0]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [h63, hc12, hc45, hlam, hphi, ht23, ht34, p77_1]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    rcases p77_3 (m.d 0 4) (by simp) with h103 | h103
                                    · linarith only [h103, h5, hlam]
                                    · linarith only [h103, h3, hlam]
                                  · have p77_0 := h77c.1
                                    have p77_1 := h77c.2.1
                                    have p77_2 := h77c.2.2.1
                                    have p77_3 := h77c.2.2.2
                                    linarith only [hlam, p77_0]
                            · linarith only [h45, h68, h72, hlam]
                          · linarith only [h3, h45, h71, hc13, hlam, hphi, u3elo0]
                      · linarith only [h4, h67, h68, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                    · linarith only [h3, h67, hc13, hlam, hphi, u3elo0]
          · linarith only [h4, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo4]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h113 | h113
        · linarith only [h1, h113, h2, hlam]
        · linarith only [h113, hlam, hphi, ht01, ht12, ht23, u0ehi7, u3elo3]
    · linarith only [h1, hlam, hphi, ht01, ht12, ht23, u0ehi6, u3elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem r1l7_20_11_13_14_M_LR_L_0_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h1elo := hb1.1
  have h4elo := hb4.1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h4, h9, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h0, h4, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h3, h8, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                    · linarith only [h0, h14, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                      · linarith only [h0, h14, h16, h5, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h0, h18, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h13, h14, h18, hc23, hlam, hphi, ht34, u4elo1]
                  · linarith only [h13, h3, hc14, hlam, hphi, u4elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
                · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                  · linarith only [h23, h5, h6, hlam]
                  · linarith only [h23, h3, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                  · linarith only [h26, h5, h6, hlam]
                  · linarith only [h26, h3, hc14, hlam, hphi, u4elo0]
            · linarith only [h4, h5, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
            · linarith only [h0, h1, h30, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
              · linarith only [h0, h1, h32, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                · rcases m.htr 1 4 5 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                          · linarith only [h0, h1, h34, h39, h4, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h35, h39, hc34, hlam, hphi, u4elo1]
                        · linarith only [h30, h35, h38, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                        · linarith only [h36, h37, h43, hlam]
                        · linarith only [h30, h35, h43, hlam]
                    · linarith only [h36, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h3, h35, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h48 | h48
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h49 | h49
                    · linarith only [h0, h1, h34, h4, h49, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h4, h49, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h3, h48, hc14, hlam, hphi, u4elo0]
        · linarith only [h3, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h55 | h55
      · rcases m.htr 0 4 5 (by decide) (by decide) with h56 | h56
        · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
          · linarith only [h1, h55, h56, h57, hlam, hphi, ht01, u0ehi9, u1elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
            · rcases m.htr 1 2 5 (by decide) (by decide) with h60 | h60
              · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h65 | h65
                        · linarith only [h0, h59, h65, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h62, h65, hc24, hlam, hphi, u4elo1]
                      · linarith only [h1, h55, h56, h64, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · linarith only [h1, h55, h56, h63, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · linarith only [h56, h62, hc14, hlam, hphi, u4elo0]
                · linarith only [h57, h59, h61, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
                · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                  · linarith only [h59, h60, h73, hlam]
                  · linarith only [h56, h73, hc14, hlam, hphi, u4elo0]
                · linarith only [h57, h59, h72, hc24, hlam, hphi, u4elo3]
            · linarith only [h1, h55, h59, hc12, hc23, hlam, hphi]
        · linarith only [h56, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8, u4elo4]
      · linarith only [h55, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6, u4elo2]
  · linarith only [h0, hlam, hphi, ht01, u0ehi5, u1elo1]

theorem r1l7_20_11_13_H_I_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases h0bigk with h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c | h10c
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10_1, u1ehi3]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        rcases p10_3 (m.d 0 1) (by simp) with h15 | h15
                        · rcases p10_3 (m.d 0 2) (by simp) with h16 | h16
                          · linarith only [h0, h16, hlam]
                          · linarith only [h0, h16, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                        · linarith only [h15, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, h4, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10_1, u1ehi3]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10_1, u1ehi3]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        rcases p10_3 (m.d 0 1) (by simp) with h24 | h24
                        · rcases p10_3 (m.d 0 2) (by simp) with h25 | h25
                          · rcases p10_3 (m.d 0 3) (by simp) with h26 | h26
                            · linarith only [h26, h3, hlam]
                            · linarith only [h26, h5, hlam]
                          · linarith only [h25, hlam, p10_0]
                        · linarith only [h0, h24, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h1, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h3, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10_1, u1ehi3]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10_1, u3elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h2, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h7, h9, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h4, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10_1, u3elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p10_1, u1ehi0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h0, h4, h6, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p10_1, u3elo0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h5, hlam, p10_0]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [h6, hlam, p10_1]
                      · have p10_0 := h10c.1
                        have p10_1 := h10c.2.1
                        have p10_2 := h10c.2.2.1
                        have p10_3 := h10c.2.2.2
                        linarith only [hlam, p10_0]
                    · linarith only [h4, h9, hc23, hlam, hphi, u3elo0]
                  · linarith only [h4, h8, hc13, hlam, hphi, u3elo0]
                · linarith only [h7, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h49 | h49
                · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                    · rcases h0bigk with h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c | h52c
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [hlam, p52_0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h0, h49, h51, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p52_1]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p52_1, u1ehi2]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p52_1, u1ehi3]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h2, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p52_1, u1ehi3]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h0, hlam, p52_0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [hlam, p52_0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h2, h5, h6, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p52_1, u1ehi3]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p52_1, u1ehi3]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h0, h2, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p52_1, u1ehi3]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h1, hlam, p52_1]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h3, hlam, p52_1]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [hlam, p52_0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p52_1, u1ehi3]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h2, h6, hlam, hphi, ht12, ht23, p52_1, u1ehi3, u3elo0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h2, hlam, p52_0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h0, h49, h51, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p52_1]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h4, hlam, p52_0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [hlam, p52_0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h6, hlam, p52_0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h5, hlam, hphi, ht12, ht23, p52_1, u1ehi0, u3elo0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h0, h49, h5, h51, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p52_1, u3elo0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h5, hlam, p52_0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [h5, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p52_1, u3elo0]
                      · have p52_0 := h52c.1
                        have p52_1 := h52c.2.1
                        have p52_2 := h52c.2.2.1
                        have p52_3 := h52c.2.2.2
                        linarith only [hlam, p52_0]
                    · linarith only [h4, h51, hc23, hlam, hphi, u3elo0]
                  · linarith only [h4, h50, hlam, hphi, ht12, ht23, u1ehi2, u3elo0]
                · linarith only [h49, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
            · linarith only [h1, h5, hlam, hphi, ht12, ht23, u1ehi2, u3elo4]
          · linarith only [h1, h4, hlam, hphi, ht12, ht23, u1ehi2, u3elo3]
        · linarith only [h0, h3, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h86 | h86
    · linarith only [h0, h86, hc12, hlam, hphi, u1ehi2]
    · linarith only [h86, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_20_11_13_M_IR_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1ehi := hb1.1
  have h3elo := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases h0bigk with h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc01, hlam, hphi, p8_1, u0ehi1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc01, hlam, hphi, p8_1, u0ehi2]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h6, hc01, hlam, hphi, p8_1, u0ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc01, hlam, hphi, p8_1, u0ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h5, h6, hc02, hlam, hphi, p8_1, u0ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h6, hc01, hlam, hphi, p8_1, u0ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, p8_1, u0ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h2, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h6, hc03, hlam, hphi, p8_1, u0ehi4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, hphi, ht01, ht12, ht23, p8_1, u0ehi4, u3elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h7, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h3, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h5, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h5, hlam, hphi, ht01, ht12, ht23, p8_1, u0ehi4, u3elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h7, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p8_1, u1ehi2]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h4, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h5, h6, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h6, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                · linarith only [h7, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
                · rcases h0bigk with h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c | h36c
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [hlam, p36_0]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [hc01, hlam, hphi, p36_1, u0ehi1]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [hc01, hlam, hphi, p36_1, u0ehi2]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [hc01, hlam, hphi, p36_1, u0ehi3]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h6, hc01, hlam, hphi, p36_1, u0ehi3]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h0, hlam, p36_0]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [hlam, p36_0]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h5, hc02, hlam, hphi, p36_1, u0ehi3]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, p36_1, u0ehi3]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h0, h6, hc01, hlam, hphi, p36_1, u0ehi3]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h1, hlam, p36_1]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h2, hlam, p36_1]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [hlam, p36_0]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [hc03, hlam, hphi, p36_1, u0ehi3]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h6, hlam, hphi, ht01, ht12, ht23, p36_1, u0ehi3, u3elo0]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h0, h35, h6, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p36_1]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h3, hlam, p36_0]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h5, hlam, p36_0]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [hlam, p36_0]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h6, hlam, p36_0]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h0, h4, hlam, p36_1]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h4, hlam, p36_1]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h0, h4, hc01, hlam, hphi, p36_1, u0ehi2]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [h6, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p36_1, u0ehi3]
                  · have p36_0 := h36c.1
                    have p36_1 := h36c.2.1
                    have p36_2 := h36c.2.2.1
                    have p36_3 := h36c.2.2.2
                    linarith only [hlam, p36_0]
                · linarith only [h35, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
            · linarith only [h5, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h64 | h64
            · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
              · linarith only [h2, h4, h64, h65, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                · rcases h0bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [hlam, p68_0]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h2, h64, hc01, hlam, hphi, p68_1, u0ehi3]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h64, hc01, hlam, hphi, p68_1, u0ehi3]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [hc01, hlam, hphi, p68_1, u0ehi3]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h2, h4, h64, hc01, hlam, hphi, p68_1, u0ehi3]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h0, hlam, p68_0]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [hlam, p68_0]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h64, hc02, hlam, hphi, p68_1, u0ehi3]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h4, hc05, hlam, hphi, p68_1, u0ehi3]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h4, hlam, p68_0]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h1, hlam, p68_1]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h2, hlam, p68_1]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [hlam, p68_0]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [hc03, hlam, hphi, p68_1, u0ehi3]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [hlam, hphi, ht01, ht12, ht23, p68_1, u0ehi4, u3elo0]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [hc04, hlam, hphi, p68_1, u0ehi0]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h3, hlam, p68_0]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h64, hlam, p68_0]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [hlam, p68_0]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h65, hlam, p68_0]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h0, h67, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p68_1, u1ehi2]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h4, hc25, hlam, hphi, ht01, ht12, p68_1, u0ehi1]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h64, h65, hc34, hc45, hlam, hphi, p68_1]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [h65, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p68_1, u0ehi3]
                  · have p68_0 := h68c.1
                    have p68_1 := h68c.2.1
                    have p68_2 := h68c.2.2.1
                    have p68_3 := h68c.2.2.2
                    linarith only [hlam, p68_0]
                · linarith only [h67, hlam, hphi, ht12, ht23, u1ehi1, u3elo2]
            · linarith only [h64, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h96 | h96
          · rcases m.htr 0 3 4 (by decide) (by decide) with h97 | h97
            · linarith only [h2, h3, h97, hlam]
            · linarith only [h97, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h100 | h100
            · linarith only [h100, h2, h3, hlam]
            · linarith only [h100, hlam, hphi, ht01, ht12, ht23, u0ehi2, u3elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, ht23, u0ehi1, u3elo2]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h105 | h105
    · linarith only [h0, h105, hc12, hlam, hphi, u1ehi2]
    · linarith only [h105, hlam, hphi, ht12, ht23, u1ehi0, u3elo1]

theorem r1l7_20_11_13_M_LI_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h0elo := hb0.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h0, h3, h5, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · linarith only [h0, h3, h8, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
            · linarith only [h0, h12, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                · linarith only [h1, h15, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h12, h14, h15, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                · linarith only [h1, h18, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                  · linarith only [h18, h2, h20, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                  · linarith only [h11, h20, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
            · linarith only [h0, h23, h3, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                · linarith only [h1, h26, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h23, h25, h26, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h29 | h29
                · linarith only [h1, h29, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                  · linarith only [h11, h2, h29, h31, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                      · linarith only [h29, h34, hc23, hlam, hphi, ht12, u1ehi2]
                      · linarith only [h0, h3, h34, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                      · linarith only [h23, h29, h37, hc23, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h0, h3, h37, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h42 | h42
    · linarith only [h0, h42, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h44 | h44
      · linarith only [h0, h44, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h46 | h46
        · rcases m.htr 0 3 5 (by decide) (by decide) with h47 | h47
          · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
            · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
              · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
                · rcases m.htr 1 3 5 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                      · linarith only [h46, h53, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                        · linarith only [h48, h50, h53, h55, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h46, h47, h55, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                    · linarith only [h44, h52, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                  · linarith only [h44, h46, h47, h50, h51, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
                · linarith only [h42, h47, h50, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h49, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h48, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
            · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
              · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
                · rcases m.htr 1 3 5 (by decide) (by decide) with h66 | h66
                  · linarith only [h42, h47, h63, h66, hc12, hlam, hphi, u1ehi0]
                  · linarith only [h65, h66, hc35, hlam, hphi, u3ehi3]
                · linarith only [h42, h65, hc34, hlam, hphi, ht12, ht23, u1ehi0]
              · linarith only [h0, h64, hc24, hlam, hphi, ht12, u1ehi0]
            · linarith only [h0, h46, h63, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1, u1ehi0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h72 | h72
          · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
            · linarith only [h0, h46, h73, hc12, hlam, hphi, u1ehi0]
            · linarith only [h0, h73, hc23, hlam, hphi, ht12, u1ehi0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h76 | h76
            · linarith only [h0, h46, h76, hc12, hlam, hphi, u1ehi0]
            · linarith only [h0, h76, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
