import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_M_IR (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases h0bigk with h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc01, hlam, hphi, p1_1, u0ehi1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc01, hlam, hphi, p1_1, u0ehi2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc01, hlam, hphi, p1_1, u0ehi3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc01, hlam, hphi, p1_1, u0ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc02, hlam, hphi, p1_1, u0ehi0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc02, hlam, hphi, p1_1, u0ehi2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc02, hlam, hphi, p1_1, u0ehi3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc02, hlam, hphi, p1_1, u0ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc03, hlam, hphi, p1_1, u0ehi0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hlam, p1_1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc02, hlam, hphi, p1_1, u0ehi3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc02, hlam, hphi, p1_1, u0ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc04, hlam, hphi, p1_1, u0ehi0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc04, hlam, hphi, p1_1, u0ehi1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc04, hlam, hphi, p1_1, u0ehi2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc04, hlam, hphi, p1_1, u0ehi4]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u0ehi0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc05, hlam, hphi, p1_1, u0ehi2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u0ehi2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u0ehi3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
  · rcases h0bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc01, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc01, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc01, hlam, hphi, p27_1, u0ehi3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc01, hlam, hphi, p27_1, u0ehi4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc01, hc23, hlam, hphi, ht12, p27_1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc23, hlam, hphi, ht01, ht12, p27_1, u0ehi3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc23, hlam, hphi, ht01, ht12, p27_1, u0ehi4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc03, hlam, hphi, p27_1, u0ehi0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc03, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc23, hlam, hphi, ht01, ht12, p27_1, u0ehi3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc23, hlam, hphi, ht01, ht12, p27_1, u0ehi4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc04, hlam, hphi, p27_1, u0ehi0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc04, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc04, hlam, hphi, p27_1, u0ehi2]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc04, hlam, hphi, p27_1, u0ehi4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u0ehi0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc05, hlam, hphi, p27_1, u0ehi1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u0ehi3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]

theorem r1l7_21_14_H_L_L_0 (m : N7Model)
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4elo := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
            · linarith only [h1, h5, h7, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
              · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                · linarith only [h1, h10, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h10, h12, h5, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h12, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
                · linarith only [h1, h15, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h15, h17, h3, h9, hc12, hlam, hphi, ht23, ht34, u4elo2]
                  · linarith only [h17, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · linarith only [h2, hc01, hlam, hphi, u1elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem r1l7_21_14_H_L_L_R (m : N7Model)
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h4ehi := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo3]

theorem r1l7_21_14_H_R_L_0 (m : N7Model)
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4elo := hb4.1
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo1]

theorem r1l7_21_14_H_R_L_R (m : N7Model)
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h4ehi := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h1, h2, h4, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht45, ht5b, u1ehi4, u4ehi4]
                · linarith only [h0, h2, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h0, h3, h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h11, h2, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                · linarith only [h0, h13, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h0, h13, h2, h4, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h4, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
        · linarith only [h3, hc35, hlam, hphi, ht12, ht23, u1ehi2]
      · linarith only [h2, hc34, hlam, hphi, ht12, ht23, u1ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht12, u1ehi1]
  · linarith only [h0, hc13, hlam, hphi, u1ehi0]

theorem r1l7_21_15_H_L_L_0 (m : N7Model)
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h5elo := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h4, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h0, h4, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
              · linarith only [h13, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                · linarith only [h1, h15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h15, h17, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h1, h12, h17, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
              · linarith only [h0, h20, h4, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
                · linarith only [h1, h22, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                  · linarith only [h12, h2, h22, h24, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                    · linarith only [h2, h26, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                          · linarith only [h20, h22, h26, h28, h30, hc12, hc23, hlam, hphi]
                          · linarith only [h20, h22, h30, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h29, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
                        · linarith only [h0, h12, h28, h34, h4, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h34, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h3, hc01, hlam, hphi, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

theorem r1l7_21_15_H_L_L_R (m : N7Model)
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h1elo := hb1.1
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
  · linarith only [h0, hc01, hlam, hphi, u1elo4]

theorem r1l7_21_15_H_R_L_0 (m : N7Model)
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h5elo := hb5.1
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo1]

theorem r1l7_21_15_H_R_L_R (m : N7Model)
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h5ehi := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h1, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
              · linarith only [h0, h1, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · linarith only [h0, h1, h2, h3, h4, h5, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
            · linarith only [h0, h1, h10, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
              · linarith only [h0, h1, h12, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
              · linarith only [h0, h1, h12, h2, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h3, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
      · linarith only [h2, hc34, hlam, hphi, ht12, ht23, u1ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht12, u1ehi1]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem r1l7_21_M_LR (m : N7Model)
    (hb1 : CMSig2_7_M_LR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h1elo := hb1.1
  have h1ehi := hb1.2.2.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1ehi5 := h1ehi (m.d 0 1) (by simp)
  have u1ehi7 := h1ehi (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u1ehi7, u1elo0]
  · linarith only [h0, hlam, hphi, u1ehi5, u1elo2]

theorem r1l7_22_13_15_H_L_L_0_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
          · linarith only [h2, h4, h6, hc23, hlam, hphi, u3elo3]
          · linarith only [h2, h6, hc23, hlam, hphi, ht34, ht45, u5elo4]
    · linarith only [h1, hc02, hlam, hphi, u2elo3]
  · linarith only [h0, hc02, hlam, hphi, u2elo2]

theorem r1l7_22_13_15_H_L_L_R_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h2 | h2
    · linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
    · linarith only [h2, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]

theorem r1l7_22_13_15_H_R_L_R_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
      · linarith only [h2, hc25, hlam, hphi, u2ehi1]
    · linarith only [h1, hc23, hlam, hphi, u2ehi0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6 | h6
    · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
      · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
        · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
          · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
            · linarith only [h10, h6, h8, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
            · linarith only [h0, h10, h6, h8, h9, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h9, hc45, hlam, hphi, ht23, ht34, u2ehi3]
        · linarith only [h8, hc34, hlam, hphi, ht23, u2ehi2]
      · linarith only [h0, h7, hc25, hlam, hphi, u2ehi0]
    · linarith only [h6, hc23, hlam, hphi, u2ehi0]

theorem r1l7_22_13_H_L_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.1
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
  · linarith only [h0, hc12, hlam, hphi, u2elo2]

theorem r1l7_22_13_H_R_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  linarith only [hlam, hphi, ht23, u2ehi2, u3elo2]

theorem r1l7_22_14_H_L_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4elo := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
          · linarith only [h2, h4, h6, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h2, h6, hc23, hlam, hphi, ht34, u4elo4]
    · linarith only [h1, hc02, hlam, hphi, u2elo3]
  · linarith only [h0, hc02, hlam, hphi, u2elo2]

theorem r1l7_22_14_H_L_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
      · linarith only [h0, h1, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi2]
    · linarith only [h1, hc12, hlam, hphi, u2elo4]
  · linarith only [h0, hc01, hlam, hphi, ht12, u2elo1]

theorem r1l7_22_14_H_R_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  linarith only [hlam, hphi, ht23, ht34, u2ehi3, u4elo2]

theorem r1l7_22_14_H_R_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
          · linarith only [h0, h2, h3, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
        · linarith only [h3, hc45, hlam, hphi, ht23, ht34, u2ehi3]
      · linarith only [h2, hc34, hlam, hphi, ht23, u2ehi2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, hc23, hlam, hphi, u2ehi1]

theorem r1l7_22_14_M_LR_L_0 (m : N7Model)
    (hb2 : CMSig2_7_M_LR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h2elo := hb2.1
  have h2ehi := hb2.2.2.1
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u2ehi6 := h2ehi (m.d 1 2) (by simp)
  have u2ehi9 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u2ehi9, u2elo1]
  · linarith only [h0, hlam, hphi, u2ehi6, u2elo4]

theorem r1l7_22_15_H_L_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi2]
  · linarith only [h0, hc02, hlam, hphi, u2elo4]

theorem r1l7_22_15_H_R_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h5elo := hb5.1
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  linarith only [hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo2]

theorem r1l7_22_M_LR (m : N7Model)
    (hb2 : CMSig2_7_M_LR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h2elo := hb2.1
  have h2ehi := hb2.2.2.1
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2ehi6 := h2ehi (m.d 1 2) (by simp)
  have u2ehi8 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u2ehi8, u2elo1]
  · linarith only [h0, hlam, hphi, u2ehi6, u2elo3]

theorem r1l7_23_M_LR (m : N7Model)
    (hb3 : CMSig2_7_M_LR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h3elo := hb3.1
  have h3ehi := hb3.2.2.1
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3ehi7 := h3ehi (m.d 2 3) (by simp)
  have u3ehi8 := h3ehi (m.d 3 4) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u3ehi8, u3elo2]
  · linarith only [h0, hlam, hphi, u3ehi7, u3elo3]

theorem r1l7_24_M_LR (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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

theorem r1l7_25_M_LI (m : N7Model)
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · rcases h5bigk with h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c | h1c
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc15, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc25, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc35, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc45, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc35, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo1]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc15, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc35, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc05, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc15, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc25, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hc45, hlam, hphi, p1_1, u5elo3]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc05, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc15, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hlam, p1_0]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [h0, hc35, hlam, hphi, p1_1, u5elo2]
    · have p1_0 := h1c.1
      have p1_1 := h1c.2.1
      have p1_2 := h1c.2.2.1
      have p1_3 := h1c.2.2.2
      linarith only [hlam, p1_0]
  · rcases h5bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc15, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc25, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc35, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc45, hlam, hphi, p27_1, u5elo0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc24, hlam, hphi, ht45, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc35, hlam, hphi, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc24, hlam, hphi, ht45, p27_1, u5elo1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo2]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc15, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc35, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hlam, p27_1]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc15, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc25, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc45, hlam, hphi, p27_1, u5elo3]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc05, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc15, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [h0, hc24, hlam, hphi, ht45, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hc35, hlam, hphi, p27_1, u5elo4]
    · have p27_0 := h27c.1
      have p27_1 := h27c.2.1
      have p27_2 := h27c.2.2.1
      have p27_3 := h27c.2.2.2
      linarith only [hlam, p27_0]

end R2N4
