import Jsp000404.S7Defs

namespace R2N4


theorem n7l_sAA2_H_L_H_R_L_0 (m : N7Model)
    (h0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (h1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  obtain ⟨h0elo, _, _⟩ := h0
  obtain ⟨h1ehi, _, _⟩ := h1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo0, u1ehi0]

theorem n7l_sAA2_H_L_H_I_L_R (m : N7Model)
    (h0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (h1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  obtain ⟨h0elo, _, _⟩ := h0
  obtain ⟨h1bigk, _, _⟩ := h1
  obtain ⟨h2ehi, _, _⟩ := h2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  rcases h1bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u0elo0, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h8 | h8
    · linarith only [h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h8, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h11 | h11
    · linarith only [h11, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h11, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h14 | h14
    · linarith only [h14, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h14, hc01, hc12, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h20 | h20
    · linarith only [h20, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h20, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h23 | h23
    · linarith only [h23, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h23, hc01, hc13, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h28 | h28
    · linarith only [h28, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h28, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h32 | h32
    · linarith only [h32, hc15, hlam, hphi, ht0b, ht5b, p0_1, u0elo0]
    · linarith only [h32, hc01, hc14, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · linarith only [h37, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h37, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h40 | h40
    · linarith only [h40, hc14, hlam, hphi, ht0b, ht45, ht5b, p0_1, u0elo0]
    · linarith only [h40, hc01, hc15, hlam, hphi, p0_1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

set_option maxHeartbeats 3960000 in
theorem n7l_sAA2_H_I_H_I_L_R (m : N7Model)
    (h0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (h1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  obtain ⟨h0bigk, _, _⟩ := h0
  obtain ⟨h2ehi, _, _⟩ := h2
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                                    · linarith only [h0, h15, h17, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                    · linarith only [h0, h15, h16, h17, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h12, h14, h16, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h0, h12, h15, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                                  · linarith only [h0, h14, h22, h23, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                                    · linarith only [h0, h14, h22, h25, h9, hc01, hc15, hlam, hphi, ht0b, ht5b]
                                    · rcases h0bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h10, h14, h3, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h10, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h10, h14, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h0, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h10, h14, h3, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h0, h10, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h0, h10, h14, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h1, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h4, hlam, p27_1]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h10, h14, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h0, h10, h14, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h2, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h5, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h22, h4, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p27_1]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h0, h10, h14, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h3, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h6, hlam, p27_1]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h7, hlam, p27_0]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [h8, hlam, p27_1]
                                      · obtain ⟨p27_0, p27_1, p27_2, p27_3⟩ := h27c
                                        linarith only [hlam, p27_0]
                                · linarith only [h1, h12, h22, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                              · linarith only [h12, h13, h54, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                                  · linarith only [h0, h54, h56, h57, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                                    · linarith only [h0, h10, h13, h4, h54, h56, h59, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h0bigk with h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h1, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h13, h59, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h13, h59, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h0, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h1, h9, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h0, h13, h59, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h0, h13, h59, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi2]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h1, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h4, hlam, p61_1]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h10, h12, h13, h59, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h0, h10, h12, h13, h4, h59, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h2, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h5, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h1, h10, h12, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h0, h10, h12, h13, h5, h59, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h3, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h6, hlam, p61_1]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h7, hlam, p61_0]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [h8, hlam, p61_1]
                                      · obtain ⟨p61_0, p61_1, p61_2, p61_3⟩ := h61c
                                        linarith only [hlam, p61_0]
                                · linarith only [h12, h13, h56, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h90 | h90
                                · linarith only [h11, h12, h88, h90, hc23, hlam, hphi, u2ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h92 | h92
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h93 | h93
                                    · rcases h0bigk with h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c | h94c
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h1, h11, h88, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h5, h90, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi2]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h11, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h0, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h1, h11, h88, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h0, h5, h90, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi2]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h0, h11, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h1, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h4, hlam, p94_1]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h11, h12, h2, h88, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h0, h11, h3, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h2, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h5, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h1, h11, h88, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h0, h11, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p94_1, u2ehi4]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h3, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h6, hlam, p94_1]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h7, hlam, p94_0]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [h8, hlam, p94_1]
                                      · obtain ⟨p94_0, p94_1, p94_2, p94_3⟩ := h94c
                                        linarith only [hlam, p94_0]
                                    · linarith only [h11, h12, h88, h92, h93, hc24, hlam, hphi, u2ehi4]
                                  · linarith only [h2, h89, h92, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h12, h88, h89, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                                · linarith only [h0, h12, h124, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h127 | h127
                                    · rcases h0bigk with h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c | h128c
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h7, h88, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h124, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h7, h88, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h7, h88, h9, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h124, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h7, h88, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h1, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h4, hlam, p128_1]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h7, h8, h88, h9, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h4, h7, h88, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h2, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h5, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h1, h9, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h0, h5, h7, h88, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p128_1, u2ehi2]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h3, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h6, hlam, p128_1]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h7, hlam, p128_0]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [h8, hlam, p128_1]
                                      · obtain ⟨p128_0, p128_1, p128_2, p128_3⟩ := h128c
                                        linarith only [hlam, p128_0]
                                    · linarith only [h0, h10, h126, h127, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h10, h123, h126, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h156 | h156
                                · linarith only [h12, h156, h9, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h158 | h158
                                  · linarith only [h10, h123, h158, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h160 | h160
                                    · linarith only [h12, h123, h160, h9, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h12, h160, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h11, h9, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h10, h9, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h165 | h165
                      · linarith only [h165, h9, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                        · linarith only [h0, h167, h4, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h169 | h169
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h170 | h170
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h173 | h173
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h174 | h174
                                    · rcases h0bigk with h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c | h175c
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h167, h172, h173, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h167, h171, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h167, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h0, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h167, h172, h173, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h0, h167, h171, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h0, h167, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h1, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h4, hlam, p175_1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h167, h173, h5, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h0, h167, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h2, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h5, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h1, h169, h174, hc04, hc45, hlam, hphi, ht0b, ht5b, p175_1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h0, h167, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p175_1, u2ehi1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h3, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h6, hlam, p175_1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h7, hlam, p175_0]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [h8, hlam, p175_1]
                                      · obtain ⟨p175_0, p175_1, p175_2, p175_3⟩ := h175c
                                        linarith only [hlam, p175_0]
                                    · rcases h0bigk with h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c | h201c
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h165, h171, h172, h174, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h171, h174, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h167, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h0, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h165, h171, h172, h174, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h0, h171, h174, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h0, h167, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h1, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h4, hlam, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h167, h6, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h0, h167, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h2, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h5, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h1, h169, h171, h174, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h0, h167, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p201_1, u2ehi1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h3, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h6, hlam, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h7, hlam, p201_0]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [h8, hlam, p201_1]
                                      · obtain ⟨p201_0, p201_1, p201_2, p201_3⟩ := h201c
                                        linarith only [hlam, p201_0]
                                  · linarith only [h1, h169, h171, h173, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h172, h9, hc34, hlam, hphi, ht23, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h229 | h229
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h230 | h230
                                  · linarith only [h165, h171, h229, h230, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h165, h230, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h229, h9, hc34, hlam, hphi, ht23, u2ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h234 | h234
                              · linarith only [h169, h170, h234, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h237 | h237
                                  · linarith only [h0, h165, h234, h236, h237, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h0, h165, h237, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h169, h170, h236, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h241 | h241
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h242 | h242
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h243 | h243
                                · linarith only [h0, h169, h241, h243, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h243, h9, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h169, h241, h242, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h247 | h247
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h248 | h248
                                · linarith only [h0, h169, h248, h4, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h248, h9, hc34, hlam, hphi, ht23, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h251 | h251
                                · linarith only [h169, h251, h9, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h251, h9, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h255 | h255
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h256 | h256
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h257 | h257
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h258 | h258
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h259 | h259
                              · linarith only [h2, h259, h8, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h261 | h261
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h262 | h262
                                  · linarith only [h0, h254, h261, h262, h8, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h264 | h264
                                    · linarith only [h0, h2, h254, h255, h261, h264, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h0bigk with h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h1, h254, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi2]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h2, h255, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h255, h259, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h0, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h1, h254, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi2]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h0, h2, h255, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h0, h255, h259, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h1, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h4, hlam, p266_1]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h2, h255, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h255, h259, h3, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h2, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h5, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h8, hc03, hc45, hlam, hphi, ht34, p266_1]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h8, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h3, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h6, hlam, p266_1]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h7, hlam, p266_0]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [h2, h255, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p266_1, u2ehi3]
                                      · obtain ⟨p266_0, p266_1, p266_2, p266_3⟩ := h266c
                                        linarith only [hlam, p266_0]
                                · linarith only [h1, h257, h261, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                              · linarith only [h257, h258, h293, h3, h8, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h295 | h295
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h296 | h296
                                  · linarith only [h255, h257, h258, h296, h7, h8, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h298 | h298
                                    · linarith only [h255, h257, h258, h295, h298, h7, h8, hc23, hlam, hphi, u2ehi3]
                                    · rcases h0bigk with h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h1, h255, h257, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h2, h255, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h255, h257, h258, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h1, h255, h257, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, h2, h255, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, h255, h257, h258, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h1, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h4, hlam, p300_1]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h2, h255, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h0, h255, h257, h258, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h2, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h5, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h1, h255, h257, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p300_1, u2ehi3]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h8, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h3, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h6, hlam, p300_1]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h7, hlam, p300_0]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [h8, hc04, hc45, hlam, hphi, p300_1]
                                      · obtain ⟨p300_0, p300_1, p300_2, p300_3⟩ := h300c
                                        linarith only [hlam, p300_0]
                                · linarith only [h257, h258, h295, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h327 | h327
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h328 | h328
                              · linarith only [h2, h328, h8, hlam]
                              · linarith only [h257, h327, h328, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
                              · linarith only [h2, h331, h8, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h333 | h333
                                · linarith only [h0, h254, h257, h333, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h335 | h335
                                  · linarith only [h2, h254, h257, h335, h8, hc24, hlam, hphi, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h337 | h337
                                    · linarith only [h2, h254, h257, h337, h8, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h254, h257, h337, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h254, h256, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h254, h255, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
                      · linarith only [h254, h342, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h342, h5, h8, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h345 | h345
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h346 | h346
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h347 | h347
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h348 | h348
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h349 | h349
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h350 | h350
                            · linarith only [h1, h350, h7, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h352 | h352
                              · linarith only [h349, h350, h352, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h354 | h354
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
                                  · linarith only [h347, h352, h355, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h357 | h357
                                    · linarith only [h0, h346, h347, h352, h354, h357, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · linarith only [h345, h357, h7, hlam]
                                · linarith only [h1, h349, h354, h7, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
                            · linarith only [h1, h361, h7, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h363 | h363
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                                · linarith only [h349, h364, h4, h7, hc13, hc35, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h366 | h366
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h367 | h367
                                    · rcases h0bigk with h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c | h368c
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h364, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h0, hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h0, h364, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h0, h1, h346, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h4, hlam, p368_1]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h345, h7, hlam, p368_1]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h7, hlam, p368_1]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h2, hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h5, hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, h7, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h3, hlam, p368_0]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h6, hlam, p368_1]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h1, h346, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p368_1, u2ehi2]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [h345, hlam, p368_1]
                                      · obtain ⟨p368_0, p368_1, p368_2, p368_3⟩ := h368c
                                        linarith only [hlam, p368_0]
                                    · linarith only [h0, h347, h366, h367, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h347, h363, h366, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h396 | h396
                                · linarith only [h346, h349, h396, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h398 | h398
                                  · linarith only [h0, h347, h363, h398, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h400 | h400
                                    · linarith only [h346, h349, h363, h400, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h346, h349, h400, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h346, h348, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h346, h347, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h346, h4, h7, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h407 | h407
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h408 | h408
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h409 | h409
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h410 | h410
                            · linarith only [h1, h410, h7, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
                              · linarith only [h2, h345, h412, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h414 | h414
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h415 | h415
                                  · linarith only [h345, h415, h5, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h417 | h417
                                    · linarith only [h2, h345, h407, h417, hc34, hlam, hphi, ht23, u2ehi3]
                                    · rcases h0bigk with h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c | h419c
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h0, h406, h414, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, h407, h409, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h2, h407, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, h407, h409, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h0, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, h407, h409, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h0, h2, h407, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h0, h1, h407, h409, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h4, hlam, p419_1]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h2, h407, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h7, hlam, p419_1]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h2, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h5, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, h407, h409, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h345, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h3, hlam, p419_0]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h6, hlam, p419_1]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h1, h407, h409, h417, h7, hc45, hlam, hphi, ht23, ht34, p419_1, u2ehi3]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [h417, h7, hc04, hc45, hlam, hphi, p419_1]
                                      · obtain ⟨p419_0, p419_1, p419_2, p419_3⟩ := h419c
                                        linarith only [hlam, p419_0]
                                · linarith only [h1, h409, h414, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h446 | h446
                            · linarith only [h409, h446, h7, hc03, hc34, hlam, hphi]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h448 | h448
                              · linarith only [h2, h345, h448, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                                · linarith only [h0, h406, h409, h450, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h452 | h452
                                  · linarith only [h345, h452, h5, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h454 | h454
                                    · linarith only [h2, h345, h406, h409, h454, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h406, h409, h454, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h406, h408, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h406, h407, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h4, h406, h7, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h462 | h462
            · linarith only [h4, h462, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h464 | h464
              · linarith only [h4, h464, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h466 | h466
                · rcases m.htr 0 4 5 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                    · linarith only [h0, h4, h468, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h470 | h470
                      · linarith only [h0, h462, h470, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
                        · linarith only [h0, h464, h472, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h474 | h474
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h475 | h475
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h479 | h479
                                    · rcases h0bigk with h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h1, h474, h479, hc01, hc45, hlam, hphi, ht0b, ht5b, p480_1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, h464, h467, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, h464, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h4, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h462, hlam, p480_1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h464, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h1, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, h4, h462, hc23, hlam, hphi, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, h4, h464, hc23, hlam, hphi, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h2, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h1, h462, h474, h479, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p480_1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, h462, h464, hc24, hlam, hphi, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h3, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p480_1, u2ehi1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h466, hlam, p480_0]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [h467, hlam, p480_1]
                                      · obtain ⟨p480_0, p480_1, p480_2, p480_3⟩ := h480c
                                        linarith only [hlam, p480_0]
                                    · rcases h0bigk with h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h3, h467, h472, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h3, h472, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h4, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h462, hlam, p506_1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h464, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h1, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, h4, h462, hc23, hlam, hphi, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h3, h4, h472, hc23, hlam, hphi, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h2, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, h4, h462, h477, hc23, hlam, hphi, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h3, h462, h476, h477, h479, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p506_1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h3, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h466, hlam, p506_0]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [h467, hlam, p506_1]
                                      · obtain ⟨p506_0, p506_1, p506_2, p506_3⟩ := h506c
                                        linarith only [hlam, p506_0]
                                  · linarith only [h1, h474, h476, h478, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h0, h4, h477, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h462, h467, h470, h476, hc24, hlam, hphi, u2ehi1]
                            · linarith only [h4, h466, h468, h475, hc23, hlam, hphi, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h536 | h536
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h537 | h537
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h538 | h538
                                · linarith only [h472, h474, h536, h538, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h4, h538, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h462, h467, h470, h537, hc24, hlam, hphi, u2ehi1]
                            · linarith only [h4, h466, h468, h536, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h543 | h543
                    · linarith only [h0, h4, h543, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h545 | h545
                      · linarith only [h0, h4, h545, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h547 | h547
                        · linarith only [h0, h462, h467, h547, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h549 | h549
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h551 | h551
                              · linarith only [h1, h462, h467, h549, h551, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h554 | h554
                                  · linarith only [h0, h462, h467, h554, hc24, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h462, h554, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h0, h4, h553, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h4, h466, h543, h550, hc23, hlam, hphi, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h559 | h559
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h560 | h560
                              · linarith only [h2, h467, h560, hlam]
                              · linarith only [h549, h559, h560, hlam]
                            · linarith only [h4, h466, h543, h559, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h564 | h564
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h565 | h565
                    · linarith only [h0, h4, h565, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h567 | h567
                      · linarith only [h0, h4, h466, h567, hc35, hlam, hphi, ht23, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h569 | h569
                        · linarith only [h0, h4, h466, h569, hc35, hlam, hphi, ht23, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h571 | h571
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h572 | h572
                            · linarith only [h1, h466, h572, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h574 | h574
                              · linarith only [h571, h572, h574, hlam]
                              · linarith only [h462, h564, h567, h574, hc24, hlam, hphi, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h577 | h577
                            · linarith only [h0, h4, h466, h571, h577, hc34, hlam, hphi, ht23, u2ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h579 | h579
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h580 | h580
                                · linarith only [h565, h571, h580, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h4, h580, hc34, hlam, hphi, ht23, u2ehi1]
                              · linarith only [h462, h564, h567, h579, hc24, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h584 | h584
                    · linarith only [h0, h4, h584, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h586 | h586
                      · linarith only [h0, h4, h586, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h588 | h588
                        · linarith only [h0, h464, h588, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h590 | h590
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h591 | h591
                            · linarith only [h1, h466, h591, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h593 | h593
                              · linarith only [h3, h462, h564, h590, h591, h593, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h596 | h596
                                  · linarith only [h0, h462, h564, h595, h596, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h0, h462, h596, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                                · linarith only [h1, h590, h595, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h600 | h600
                            · linarith only [h2, h466, h564, h590, h600, hc03, hc45, hlam, hphi, ht34]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h602 | h602
                              · linarith only [h2, h564, h602, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h604 | h604
                                · linarith only [h584, h590, h604, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h4, h604, hc34, hlam, hphi, ht23, u2ehi0]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h607 | h607
          · rcases m.htr 0 2 4 (by decide) (by decide) with h608 | h608
            · rcases m.htr 0 2 5 (by decide) (by decide) with h609 | h609
              · linarith only [h0, h3, h609, hlam]
              · linarith only [h607, h609, hc25, hlam, hphi, u2ehi2]
            · linarith only [h607, h608, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h613 | h613
            · linarith only [h607, h613, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h615 | h615
              · linarith only [h607, h615, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h617 | h617
                · linarith only [h1, h3, h617, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h619 | h619
                  · linarith only [h2, h3, h619, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h621 | h621
                    · linarith only [h0, h613, h619, h621, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h623 | h623
                      · linarith only [h1, h3, h613, h621, h623, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h625 | h625
                        · linarith only [h0, h607, h625, hc23, hlam, hphi, u2ehi4]
                        · linarith only [h1, h3, h621, h625, hc25, hlam, hphi, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h628 | h628
        · rcases m.htr 0 2 3 (by decide) (by decide) with h629 | h629
          · rcases m.htr 0 2 4 (by decide) (by decide) with h630 | h630
            · linarith only [h0, h2, h630, hlam]
            · linarith only [h629, h630, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h633 | h633
            · linarith only [h629, h633, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h635 | h635
              · linarith only [h629, h635, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h637 | h637
                · rcases m.htr 0 4 5 (by decide) (by decide) with h638 | h638
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h639 | h639
                    · linarith only [h0, h629, h639, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h641 | h641
                      · linarith only [h0, h629, h641, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h0, h2, h641, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h638, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h645 | h645
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h646 | h646
                    · linarith only [h0, h2, h646, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h648 | h648
                      · linarith only [h1, h2, h646, h648, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1, h2, h646, h648, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h645, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h652 | h652
          · rcases m.htr 0 2 4 (by decide) (by decide) with h653 | h653
            · linarith only [h0, h2, h653, hlam]
            · linarith only [h652, h653, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h656 | h656
            · linarith only [h652, h656, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h658 | h658
              · linarith only [h652, h658, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h660 | h660
                · linarith only [h1, h628, h660, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h662 | h662
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h663 | h663
                    · linarith only [h0, h2, h663, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h665 | h665
                      · linarith only [h1, h2, h656, h663, h665, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h0, h2, h665, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h662, hc45, hlam, hphi, ht23, ht34, u2ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h669 | h669
      · rcases m.htr 0 1 5 (by decide) (by decide) with h670 | h670
        · rcases m.htr 0 2 3 (by decide) (by decide) with h671 | h671
          · linarith only [h0, h1, h671, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h673 | h673
            · linarith only [h671, h673, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h675 | h675
              · linarith only [h671, h675, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h677 | h677
                · rcases m.htr 0 4 5 (by decide) (by decide) with h678 | h678
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h679 | h679
                    · linarith only [h0, h671, h679, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h679, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h682 | h682
                    · linarith only [h0, h1, h682, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h682, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h677, hc35, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h686 | h686
          · linarith only [h0, h1, h686, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h688 | h688
            · linarith only [h686, h688, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h690 | h690
              · linarith only [h686, h690, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h692 | h692
                · rcases m.htr 0 4 5 (by decide) (by decide) with h693 | h693
                  · linarith only [h669, h670, h693, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h695 | h695
                    · linarith only [h0, h1, h695, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h695, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h692, hc35, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h699 | h699
        · rcases m.htr 0 2 3 (by decide) (by decide) with h700 | h700
          · linarith only [h0, h1, h700, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h702 | h702
            · linarith only [h700, h702, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h704 | h704
              · linarith only [h700, h704, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h706 | h706
                · rcases m.htr 0 4 5 (by decide) (by decide) with h707 | h707
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h708 | h708
                    · linarith only [h0, h1, h700, h708, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h708, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h669, h707, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h706, hc35, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h713 | h713
          · linarith only [h0, h1, h713, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h715 | h715
            · linarith only [h713, h715, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h717 | h717
              · linarith only [h713, h717, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h719 | h719
                · rcases m.htr 0 4 5 (by decide) (by decide) with h720 | h720
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h721 | h721
                    · linarith only [h0, h1, h713, h721, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h721, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h669, h720, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h719, hc35, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h726 | h726
    · rcases m.htr 0 1 4 (by decide) (by decide) with h727 | h727
      · rcases m.htr 0 1 5 (by decide) (by decide) with h728 | h728
        · rcases m.htr 0 2 3 (by decide) (by decide) with h729 | h729
          · rcases m.htr 0 2 4 (by decide) (by decide) with h730 | h730
            · rcases m.htr 0 2 5 (by decide) (by decide) with h731 | h731
              · rcases m.htr 0 3 5 (by decide) (by decide) with h732 | h732
                · rcases m.htr 0 4 5 (by decide) (by decide) with h733 | h733
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h734 | h734
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h735 | h735
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h736 | h736
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h737 | h737
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h738 | h738
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h739 | h739
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h740 | h740
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h741 | h741
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h742 | h742
                                    · linarith only [h0, h726, h734, h740, h742, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h0, h726, h737, h739, h742, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h0, h726, h737, h739, h741, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h726, h737, h740, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h0, h727, h733, h735, h739, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h0, h726, h732, h737, h738, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h749 | h749
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h750 | h750
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h751 | h751
                                · linarith only [h736, h737, h749, h751, hc23, hlam, hphi, u2ehi4]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h753 | h753
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h754 | h754
                                    · rcases h0bigk with h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c | h755c
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, hlam, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, h726, h736, h749, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, h727, h736, h737, h749, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, h728, h736, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h726, hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h729, hlam, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h727, h736, h737, h749, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h726, h728, h736, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h727, hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h730, hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h726, h736, h749, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h0, h727, h728, h736, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p755_1, u2ehi4]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h728, hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h731, hlam, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h732, hlam, p755_0]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [h733, hlam, p755_1]
                                      · obtain ⟨p755_0, p755_1, p755_2, p755_3⟩ := h755c
                                        linarith only [hlam, p755_0]
                                    · linarith only [h736, h737, h749, h754, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                  · linarith only [h0, h727, h750, h751, h753, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h0, h727, h733, h735, h750, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h0, h726, h732, h734, h749, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h726, h734, h736, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h734, h735, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h727, h730, h734, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h789 | h789
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h790 | h790
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h791 | h791
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h792 | h792
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h793 | h793
                              · linarith only [h727, h733, h793, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h795 | h795
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h796 | h796
                                  · linarith only [h727, h733, h789, h796, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h798 | h798
                                    · linarith only [h727, h733, h789, h795, h798, hc23, hlam, hphi, u2ehi3]
                                    · rcases h0bigk with h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, hlam, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, h727, h789, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, h727, h733, h789, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, h726, h789, h792, h793, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, h727, h789, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h0, h727, h733, h789, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h726, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h729, hlam, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h727, h789, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h726, h727, h733, h789, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h727, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h730, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h733, hc03, hc45, hlam, hphi, ht34, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h733, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h728, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h731, hlam, p800_1]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h732, hlam, p800_0]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [h727, h789, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi3]
                                      · obtain ⟨p800_0, p800_1, p800_2, p800_3⟩ := h800c
                                        linarith only [hlam, p800_0]
                                · linarith only [h0, h726, h791, h795, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h726, h732, h791, h792, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h828 | h828
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h829 | h829
                              · linarith only [h0, h727, h728, h733, h790, h829, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                              · linarith only [h791, h828, h829, hlam]
                            · linarith only [h0, h726, h732, h788, h828, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h726, h788, h790, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h788, h789, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h727, h730, h788, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h836 | h836
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h837 | h837
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h838 | h838
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h839 | h839
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h840 | h840
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h841 | h841
                            · linarith only [h726, h732, h841, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h843 | h843
                              · linarith only [h840, h841, h843, hlam]
                              · linarith only [h0, h727, h836, h838, h843, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h846 | h846
                            · linarith only [h726, h732, h846, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h848 | h848
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h849 | h849
                                · linarith only [h837, h840, h849, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h851 | h851
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h852 | h852
                                    · rcases h0bigk with h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c | h853c
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, h726, h732, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h727, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, h729, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, h730, h849, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h0, h729, h732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h726, hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h729, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h732, h836, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h732, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h727, hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h730, hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h726, h837, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h726, h732, h837, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h728, hlam, p853_0]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h731, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h726, h837, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p853_1, u2ehi2]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [h836, hlam, p853_1]
                                      · obtain ⟨p853_0, p853_1, p853_2, p853_3⟩ := h853c
                                        linarith only [hlam, p853_0]
                                    · linarith only [h0, h727, h838, h851, h852, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h0, h727, h836, h851, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h0, h727, h836, h838, h848, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h726, h837, h839, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h727, h731, h836, h838, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h727, h730, h837, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h885 | h885
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h886 | h886
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h887 | h887
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h888 | h888
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h889 | h889
                            · linarith only [h726, h732, h889, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h891 | h891
                              · linarith only [h727, h836, h891, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h893 | h893
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h894 | h894
                                  · linarith only [h727, h836, h886, h894, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h896 | h896
                                    · linarith only [h0, h727, h728, h836, h885, h886, h889, h893, h896, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h0bigk with h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, hlam, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h727, h886, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi3]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h726, h732, h885, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi2]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h726, h885, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi2]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h727, h886, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi3]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h726, h732, h885, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi2]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h726, hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h729, hlam, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h727, h886, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi3]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h732, hlam, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h727, hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h730, hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h726, h886, h888, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi3]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h836, hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h728, hlam, p898_0]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h731, hlam, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h726, h728, h886, h888, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p898_1, u2ehi3]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [h0, h728, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p898_1]
                                      · obtain ⟨p898_0, p898_1, p898_2, p898_3⟩ := h898c
                                        linarith only [hlam, p898_0]
                                · linarith only [h0, h726, h888, h893, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h925 | h925
                            · linarith only [h726, h732, h925, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h927 | h927
                              · linarith only [h727, h836, h927, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h929 | h929
                                · linarith only [h729, h732, h888, h929, hc13, hc35, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h931 | h931
                                  · linarith only [h727, h836, h886, h931, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h933 | h933
                                    · linarith only [h727, h836, h885, h888, h933, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h885, h888, h933, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h726, h885, h887, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h885, h886, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h728, h731, h885, hc23, hlam, hphi, u2ehi4]
              · linarith only [h729, h731, hc25, hlam, hphi, u2ehi2]
            · linarith only [h729, h730, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h726, h729, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h942 | h942
          · rcases m.htr 0 2 4 (by decide) (by decide) with h943 | h943
            · rcases m.htr 0 2 5 (by decide) (by decide) with h944 | h944
              · rcases m.htr 0 3 5 (by decide) (by decide) with h945 | h945
                · linarith only [h726, h728, h945, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h947 | h947
                  · linarith only [h727, h728, h947, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h949 | h949
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h950 | h950
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h951 | h951
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h952 | h952
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h953 | h953
                            · linarith only [h726, h728, h945, h951, h953, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h726, h728, h950, h952, h953, hc35, hlam, hphi, ht23, u2ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h956 | h956
                            · linarith only [h726, h945, h956, hlam]
                            · linarith only [h726, h728, h949, h956, hc35, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h0, h726, h949, h951, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h949, h950, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h944, h949, hc23, hlam, hphi, u2ehi4]
              · linarith only [h942, h944, hc25, hlam, hphi, u2ehi2]
            · linarith only [h942, h943, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h726, h942, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h965 | h965
        · rcases m.htr 0 2 3 (by decide) (by decide) with h966 | h966
          · rcases m.htr 0 2 4 (by decide) (by decide) with h967 | h967
            · rcases m.htr 0 2 5 (by decide) (by decide) with h968 | h968
              · rcases m.htr 0 3 5 (by decide) (by decide) with h969 | h969
                · rcases m.htr 0 4 5 (by decide) (by decide) with h970 | h970
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h971 | h971
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h972 | h972
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h973 | h973
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h974 | h974
                          · linarith only [h726, h727, h974, hlam]
                          · linarith only [h726, h727, h971, h974, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h726, h727, h971, h972, h973, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h967, h971, h972, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h726, h968, h969, h971, hc23, hlam, hphi, u2ehi4]
                  · linarith only [h726, h727, h969, h970, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h981 | h981
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h982 | h982
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h983 | h983
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h984 | h984
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h985 | h985
                          · linarith only [h726, h727, h985, hlam]
                          · linarith only [h726, h727, h982, h985, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h726, h727, h982, h983, h984, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h726, h982, h983, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h967, h982, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h727, h965, h981, hlam]
              · linarith only [h967, h968, hc25, hlam, hphi, u2ehi3]
            · linarith only [h966, h967, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h726, h966, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h995 | h995
          · rcases m.htr 0 2 4 (by decide) (by decide) with h996 | h996
            · rcases m.htr 0 2 5 (by decide) (by decide) with h997 | h997
              · rcases m.htr 0 3 5 (by decide) (by decide) with h998 | h998
                · linarith only [h726, h965, h998, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1000 | h1000
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1001 | h1001
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1002 | h1002
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1003 | h1003
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1004 | h1004
                          · linarith only [h1004, h726, h727, hlam]
                          · linarith only [h1001, h1004, h726, h727, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h1001, h1002, h1003, h726, h727, h997, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h1001, h1002, h726, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1001, h996, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1010 | h1010
                    · linarith only [h1000, h1010, h726, h727, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h1010, h997, hc23, hlam, hphi, u2ehi4]
              · linarith only [h995, h997, hc25, hlam, hphi, u2ehi2]
            · linarith only [h995, h996, hc24, hlam, hphi, u2ehi2]
          · linarith only [h0, h726, h995, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1016 | h1016
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1017 | h1017
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1018 | h1018
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1019 | h1019
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1020 | h1020
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1021 | h1021
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1022 | h1022
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1023 | h1023
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1024 | h1024
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1025 | h1025
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1026 | h1026
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1027 | h1027
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1028 | h1028
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1029 | h1029
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1030 | h1030
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1031 | h1031
                                    · rcases h0bigk with h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h0, hlam, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h726, hlam, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, h1022, h1023, h1025, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, h1023, h1025, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1016, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h0, h1017, h1025, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h0, h1019, h1030, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h0, h1017, h1025, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, h1025, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1018, hlam, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, h1022, h1023, h1025, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, h1023, h1025, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1016, hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1019, hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1016, h1024, h1030, h726, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1016, h1017, h1025, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi4]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1017, hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1020, hlam, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1021, hlam, p1032_0]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [h1022, hlam, p1032_1]
                                      · obtain ⟨p1032_0, p1032_1, p1032_2, p1032_3⟩ := h1032c
                                        linarith only [hlam, p1032_0]
                                    · linarith only [h1016, h1023, h1028, h1031, h726, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h1016, h1023, h1028, h1030, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h1016, h1023, h1026, h1029, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h1016, h1022, h1023, h1024, h1028, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h1016, h1024, h1027, h726, hc35, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1016, h1024, h1026, h726, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h1016, h1024, h1025, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h1016, h1019, h1023, h1024, h726, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h1016, h1020, h1022, h1023, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1067 | h1067
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1068 | h1068
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1069 | h1069
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1070 | h1070
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1071 | h1071
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1072 | h1072
                              · linarith only [h1016, h1022, h1072, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1074 | h1074
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1075 | h1075
                                  · linarith only [h1016, h1022, h1068, h1075, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1077 | h1077
                                    · linarith only [h1016, h1022, h1068, h1074, h1077, hlam]
                                    · rcases h0bigk with h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, hlam, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h726, hlam, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1016, h1068, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1016, h1022, h1068, h726, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, h726, hc01, hc12, hlam, hphi, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, h1016, h1068, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, h1016, h1022, h1068, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1017, h1068, h1072, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1018, hlam, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, h1016, h1018, h1068, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h0, h1016, h1018, h1022, h1068, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1016, hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1019, hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1022, hc03, hc45, hlam, hphi, ht34, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1022, hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1017, hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1020, hlam, p1079_1]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1021, hlam, p1079_0]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [h1016, h1021, h1068, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1079_1, u2ehi3]
                                      · obtain ⟨p1079_0, p1079_1, p1079_2, p1079_3⟩ := h1079c
                                        linarith only [hlam, p1079_0]
                                · linarith only [h1016, h1022, h1070, h1074, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h1016, h1019, h1071, h726, hc35, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1016, h1019, h1070, h726, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h1016, h1020, h1067, h1068, h1069, h726, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1017, h1020, h1067, h1068, h726, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1017, h1019, h1022, h1067, hc23, hlam, hphi, u2ehi3]
                · linarith only [h1017, h1021, h726, hlam]
              · linarith only [h1018, h1020, hc25, hlam, hphi, u2ehi2]
            · linarith only [h1018, h1019, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1114 | h1114
            · linarith only [h1018, h1114, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h1016, h1114, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1117 | h1117
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1118 | h1118
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1119 | h1119
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1120 | h1120
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1121 | h1121
                  · linarith only [h1016, h1017, h1121, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1123 | h1123
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1124 | h1124
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1125 | h1125
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1126 | h1126
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1127 | h1127
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1128 | h1128
                              · linarith only [h1016, h1017, h1121, h1123, h1127, h1128, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h1016, h1017, h1124, h1128, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                            · linarith only [h0, h1016, h1117, h1120, h1124, h1127, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h1016, h1124, h1126, h726, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h1016, h1119, h1120, h1124, h1125, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h1117, h1124, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1016, h1118, h1123, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1136 | h1136
                  · linarith only [h1016, h1120, h1136, h726, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1138 | h1138
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1139 | h1139
                      · linarith only [h1016, h1120, h1139, h726, hc35, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h0, h1117, h1139, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1117, h1138, hlam]
              · linarith only [h1117, h1119, hc25, hlam, hphi, u2ehi2]
            · linarith only [h1117, h1118, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1145 | h1145
            · linarith only [h1117, h1145, hc23, hlam, hphi, u2ehi3]
            · linarith only [h0, h1016, h1145, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1148 | h1148
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1149 | h1149
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1150 | h1150
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1151 | h1151
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1152 | h1152
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1153 | h1153
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1154 | h1154
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1155 | h1155
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1156 | h1156
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1157 | h1157
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1158 | h1158
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1159 | h1159
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1160 | h1160
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1161 | h1161
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1162 | h1162
                                    · rcases h0bigk with h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c | h1163c
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h726, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1016, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1016, h1154, h1157, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1148, h1156, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, h1148, h1156, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, h1016, h1148, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, h1148, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1148, h1156, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1149, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1016, h1148, h1156, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, h1148, h1149, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1148, h1156, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1150, hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1148, h1156, h726, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h0, h1148, h1150, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1163_1, u2ehi4]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1148, hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1151, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1152, hlam, p1163_0]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [h1153, hlam, p1163_1]
                                      · obtain ⟨p1163_0, p1163_1, p1163_2, p1163_3⟩ := h1163c
                                        linarith only [hlam, p1163_0]
                                    · rcases h0bigk with h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h0, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h726, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1016, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1148, h1156, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h0, h1149, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi2]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h0, h1016, h1148, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h0, h1148, h1156, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1148, h1156, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1149, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1016, h1148, h1154, h1156, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1148, h1154, h1156, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1148, h1156, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1150, hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1016, h1148, h1154, h1156, h1157, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1016, h1148, h1154, h1156, h1157, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1189_1, u2ehi4]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1148, hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1151, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1152, hlam, p1189_0]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [h1153, hlam, p1189_1]
                                      · obtain ⟨p1189_0, p1189_1, p1189_2, p1189_3⟩ := h1189c
                                        linarith only [hlam, p1189_0]
                                  · linarith only [h1016, h1148, h1154, h1157, h1159, h1161, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1216 | h1216
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1217 | h1217
                                    · rcases h0bigk with h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h0, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h726, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1016, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1016, h1154, h1157, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h0, h1148, h726, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h0, h1016, h1148, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h0, h1151, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1148, h1151, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1149, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1016, h1148, h1154, h1156, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1148, h1154, h1156, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1148, h1156, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1150, hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1016, h1148, h1154, h1156, h1157, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1016, h1148, h1154, h1156, h1157, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1218_1, u2ehi4]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1148, hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1151, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1152, hlam, p1218_0]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [h1153, hlam, p1218_1]
                                      · obtain ⟨p1218_0, p1218_1, p1218_2, p1218_3⟩ := h1218c
                                        linarith only [hlam, p1218_0]
                                    · linarith only [h1160, h1216, h1217, hc24, hlam, hphi, u2ehi2]
                                  · linarith only [h0, h1148, h1159, h1216, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h1016, h1148, h1153, h1159, hlam]
                            · linarith only [h1016, h1148, h1156, h1157, h1158, hc35, hlam, hphi, ht23, u2ehi4]
                          · linarith only [h1148, h1156, h1157, h726, hc34, hlam, hphi, ht23, u2ehi4]
                        · linarith only [h0, h1149, h1156, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h1148, h1151, h1154, h1155, h726, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1148, h1149, h1151, h1154, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                  · linarith only [h1016, h1148, h1153, hlam]
                · linarith only [h1148, h1152, h726, hlam]
              · linarith only [h1149, h1151, hc25, hlam, hphi, u2ehi2]
            · linarith only [h1149, h1150, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1256 | h1256
            · linarith only [h1149, h1256, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1258 | h1258
              · linarith only [h1149, h1258, hc23, hlam, hphi, u2ehi4]
              · linarith only [h0, h1148, h1258, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1261 | h1261
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1262 | h1262
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1263 | h1263
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1264 | h1264
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1265 | h1265
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1266 | h1266
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1267 | h1267
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1268 | h1268
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1269 | h1269
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1270 | h1270
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1271 | h1271
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1272 | h1272
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1273 | h1273
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1274 | h1274
                                    · rcases h0bigk with h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h726, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1016, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1148, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, h1148, h1264, hc01, hc12, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, h1148, h1265, hc01, hc12, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h726, hc01, hc13, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1261, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, h1261, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1275_1, u2ehi3]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h0, h1261, h1263, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1275_1, u2ehi4]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1016, hc01, hc14, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1262, hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1016, h1266, h1269, h726, hc01, hc12, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1016, h1263, h1266, h1269, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1275_1, u2ehi4]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1148, hc01, hc15, hlam, hphi, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1263, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1264, hlam, p1275_0]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [h1265, hlam, p1275_1]
                                      · obtain ⟨p1275_0, p1275_1, p1275_2, p1275_3⟩ := h1275c
                                        linarith only [hlam, p1275_0]
                                    · rcases h0bigk with h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c | h1301c
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h0, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h726, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1016, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1148, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h0, h1261, h1272, h1273, h1274, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h0, h1016, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1266, h726, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1261, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1262, h1266, h1273, h1274, h726, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1263, h1266, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1301_1, u2ehi4]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1016, h1266, h1269, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1262, hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1016, h1266, h1269, h726, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1016, h1263, h1266, h1269, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1301_1, u2ehi4]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1148, h1266, h1269, h1271, hc01, hc12, hlam, hphi, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1263, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1264, hlam, p1301_0]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [h1265, hlam, p1301_1]
                                      · obtain ⟨p1301_0, p1301_1, p1301_2, p1301_3⟩ := h1301c
                                        linarith only [hlam, p1301_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1327 | h1327
                                    · linarith only [h1273, h1327, hc34, hlam, hphi, ht23, u2ehi3]
                                    · rcases h0bigk with h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c | h1329c
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h0, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h726, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1016, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1148, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h0, h726, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h0, h1265, h1273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1329_1, u2ehi3]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1266, h726, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1261, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1265, h1266, h1273, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1329_1, u2ehi3]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1265, h1266, h1273, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1329_1, u2ehi3]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1016, h1266, h1269, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1262, hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1016, h1266, h1269, h726, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1016, h1265, h1266, h1269, h1273, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1329_1, u2ehi3]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1148, h1266, h1269, h1271, hc01, hc12, hlam, hphi, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1263, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1264, hlam, p1329_0]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [h1265, hlam, p1329_1]
                                      · obtain ⟨p1329_0, p1329_1, p1329_2, p1329_3⟩ := h1329c
                                        linarith only [hlam, p1329_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1355 | h1355
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1356 | h1356
                                    · rcases h0bigk with h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h0, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h726, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1016, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1148, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h0, h726, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h0, h1016, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1266, h726, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1261, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1262, h1266, h1355, h726, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1263, h1266, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1357_1, u2ehi4]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1016, h1266, h1269, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1262, hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1016, h1266, h1269, h726, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1016, h1263, h1266, h1269, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1357_1, u2ehi4]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1148, h1266, h1269, h1271, hc01, hc12, hlam, hphi, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1263, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1264, hlam, p1357_0]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [h1265, hlam, p1357_1]
                                      · obtain ⟨p1357_0, p1357_1, p1357_2, p1357_3⟩ := h1357c
                                        linarith only [hlam, p1357_0]
                                    · linarith only [h1272, h1356, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1384 | h1384
                                    · linarith only [h1266, h1269, h1272, h1355, h1384, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                    · linarith only [h1272, h1384, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h1016, h1265, h1271, hlam]
                            · linarith only [h1264, h1270, h726, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1389 | h1389
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1390 | h1390
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1391 | h1391
                                · linarith only [h1261, h1264, h1269, h1391, h726, hc02, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1393 | h1393
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1394 | h1394
                                    · rcases h0bigk with h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c | h1395c
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h0, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h726, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1016, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1148, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h0, h1264, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h0, h1016, hc01, hc12, hlam, hphi, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h0, h1263, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1395_1, u2ehi4]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1269, h726, hc01, hc34, hlam, hphi, ht12, ht23, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1261, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1269, h726, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1263, h1269, h726, hc34, hlam, hphi, ht23, p1395_1, u2ehi4]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1016, h1269, hc01, hc34, hlam, hphi, ht12, ht23, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1262, hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1016, h1269, hc03, hc34, hlam, hphi, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1016, h1263, h1269, hc34, hlam, hphi, ht23, p1395_1, u2ehi4]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1148, hc01, hc15, hlam, hphi, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1263, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1264, hlam, p1395_0]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [h1265, hlam, p1395_1]
                                      · obtain ⟨p1395_0, p1395_1, p1395_2, p1395_3⟩ := h1395c
                                        linarith only [hlam, p1395_0]
                                    · linarith only [h1269, h1394, h726, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                  · linarith only [h1264, h1265, h1269, h1391, h1393, h726, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h1016, h1264, h1265, h1269, h1390, h726, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1264, h1389, h726, hlam]
                        · linarith only [h0, h1261, h1268, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h1263, h1267, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1263, h1266, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1428 | h1428
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1429 | h1429
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1430 | h1430
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1431 | h1431
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1432 | h1432
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1433 | h1433
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1434 | h1434
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1435 | h1435
                                  · linarith only [h1262, h1265, h1435, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1437 | h1437
                                    · linarith only [h1262, h1265, h1434, h1437, hlam]
                                    · rcases h0bigk with h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h0, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h726, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1016, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1148, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h0, h1261, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi2]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h0, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h0, h1262, h1265, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1428, h726, hc01, hc12, hlam, hphi, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1261, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1262, h1428, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1262, h1265, h1428, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1016, h1428, h1431, hc01, hc12, hlam, hphi, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1262, hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1265, h1428, h1431, h1433, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1265, hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1265, h1428, h1431, h1433, hc01, hc12, hlam, hphi, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1263, hlam, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1264, hlam, p1439_0]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [h1265, h1428, h1431, h1433, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1439_1]
                                      · obtain ⟨p1439_0, p1439_1, p1439_2, p1439_3⟩ := h1439c
                                        linarith only [hlam, p1439_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1465 | h1465
                                  · linarith only [h0, h1016, h1262, h1265, h1465, hc01, hc12, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1467 | h1467
                                    · linarith only [h1262, h1265, h1434, h1467, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h1434, h1467, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1470 | h1470
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1471 | h1471
                                  · linarith only [h1016, h1433, h1470, h1471, hc01, hc23, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1473 | h1473
                                    · linarith only [h1016, h1262, h1433, h1470, h1473, hc23, hlam, hphi, u2ehi3]
                                    · rcases h0bigk with h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h0, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h726, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1016, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1148, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h0, h726, hc01, hc12, hlam, hphi, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h0, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1475_1, u2ehi3]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h0, h1262, h1265, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1475_1, u2ehi3]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1428, h726, hc01, hc12, hlam, hphi, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1261, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1262, h1428, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1475_1, u2ehi3]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1262, h1265, h1428, h726, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1475_1, u2ehi3]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1016, hc01, hc14, hlam, hphi, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1262, hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1016, h1433, hc03, hc45, hlam, hphi, ht34, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1265, hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1148, h1433, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1263, hlam, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1264, hlam, p1475_0]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [h1016, h1264, h1428, h726, hc01, hc12, hlam, hphi, p1475_1]
                                      · obtain ⟨p1475_0, p1475_1, p1475_2, p1475_3⟩ := h1475c
                                        linarith only [hlam, p1475_0]
                                · linarith only [h1431, h1433, h1470, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h1264, h1432, h726, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1503 | h1503
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1504 | h1504
                              · linarith only [h1262, h1265, h1431, h1504, hc34, hlam, hphi, ht23, u2ehi3]
                              · linarith only [h1431, h1503, h1504, hlam]
                            · linarith only [h1264, h1503, h726, hlam]
                        · linarith only [h0, h1263, h1430, hlam]
                      · linarith only [h0, h1263, h1429, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1263, h1428, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1511 | h1511
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1512 | h1512
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1513 | h1513
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1514 | h1514
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1515 | h1515
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1516 | h1516
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1517 | h1517
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1518 | h1518
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1519 | h1519
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1520 | h1520
                                    · linarith only [h1261, h1264, h1512, h1516, h1518, h1520, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h1261, h1264, h1512, h1516, h1518, h1519, h1520, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1523 | h1523
                                    · linarith only [h1519, h1523, hc34, hlam, hphi, ht23, u2ehi3]
                                    · linarith only [h1264, h1511, h1523, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1526 | h1526
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1527 | h1527
                                    · rcases h0bigk with h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c | h1528c
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [hlam, p1528_0]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h0, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h726, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1016, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1148, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [hlam, p1528_0]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h0, h1261, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1528_1, u2ehi2]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h0, h1016, hc01, hc12, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1512, h726, hc01, hc12, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1261, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [hlam, p1528_0]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1264, h1511, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1264, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1016, hc01, hc14, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1262, hlam, p1528_0]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1016, h1261, h1512, h1515, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1528_1, u2ehi2]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [hlam, p1528_0]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1016, h1261, h1264, h1512, h1515, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1528_1, u2ehi2]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1148, hc01, hc15, hlam, hphi, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1263, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1261, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1528_1, u2ehi2]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [h1511, hlam, p1528_1]
                                      · obtain ⟨p1528_0, p1528_1, p1528_2, p1528_3⟩ := h1528c
                                        linarith only [hlam, p1528_0]
                                    · linarith only [h1518, h1527, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1555 | h1555
                                    · linarith only [h1512, h1515, h1526, h1555, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · linarith only [h1518, h1555, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h1016, h1511, h1517, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1559 | h1559
                              · linarith only [h1515, h1516, h1559, hlam]
                              · linarith only [h1016, h1511, h1559, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1562 | h1562
                            · linarith only [h1261, h1264, h1515, h1562, hc34, hlam, hphi, ht23, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1564 | h1564
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1565 | h1565
                                · linarith only [h1261, h1515, h1565, h726, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1567 | h1567
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1568 | h1568
                                    · rcases h0bigk with h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c | h1569c
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [hlam, p1569_0]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h0, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h726, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1016, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1148, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [hlam, p1569_0]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h0, h1261, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1569_1, u2ehi2]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h0, h1016, hc01, hc12, hlam, hphi, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h726, hc01, hc13, hlam, hphi, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1261, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [hlam, p1569_0]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1262, h1567, hc03, hc45, hlam, hphi, ht0b, ht5b, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1264, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1016, h1515, hc01, hc34, hlam, hphi, ht12, ht23, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1262, hlam, p1569_0]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1016, h1261, h1515, hc34, hlam, hphi, ht23, p1569_1, u2ehi2]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [hlam, p1569_0]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1016, h1261, h1264, h1515, hc34, hlam, hphi, ht23, p1569_1, u2ehi2]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1148, h1515, h1564, hc01, hc34, hlam, hphi, ht12, ht23, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1263, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1148, h1261, h1515, h1564, hc34, hlam, hphi, ht23, p1569_1, u2ehi2]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [h1511, hlam, p1569_1]
                                      · obtain ⟨p1569_0, p1569_1, p1569_2, p1569_3⟩ := h1569c
                                        linarith only [hlam, p1569_0]
                                    · linarith only [h1016, h1511, h1515, h1568, hlam]
                                  · linarith only [h1016, h1511, h1515, h1565, h1567, hc34, hlam, hphi, ht23, u2ehi2]
                              · linarith only [h1016, h1511, h1564, hlam]
                        · linarith only [h0, h1261, h1514, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h1263, h1513, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1263, h1512, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1601 | h1601
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1602 | h1602
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1603 | h1603
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1604 | h1604
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1605 | h1605
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1606 | h1606
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1607 | h1607
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1608 | h1608
                                  · linarith only [h1262, h1511, h1608, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1610 | h1610
                                    · linarith only [h1261, h1264, h1511, h1601, h1605, h1607, h1610, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c | h1612c
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h0, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h726, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1016, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1148, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h0, h1261, h1607, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h0, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1612_1, u2ehi3]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1601, h726, hc01, hc12, hlam, hphi, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1261, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1262, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1612_1, u2ehi3]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1264, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1016, h1601, h1604, hc01, hc12, hlam, hphi, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1262, hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1511, h1601, h1604, h1606, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1511, hlam, p1612_0]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1264, h1601, h1604, h1606, h1610, hc01, hc12, hlam, hphi, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1263, hlam, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1261, h1264, h1601, h1604, h1606, h1607, h1610, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1612_1, u2ehi3]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [h1264, h1601, h1604, h1606, h1610, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1612_1]
                                      · obtain ⟨p1612_0, p1612_1, p1612_2, p1612_3⟩ := h1612c
                                        linarith only [hlam, p1612_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1638 | h1638
                                  · linarith only [h0, h1016, h1262, h1511, h1638, hc01, hc12, hlam, hphi]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1640 | h1640
                                    · linarith only [h1262, h1511, h1607, h1640, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h1607, h1640, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1643 | h1643
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1644 | h1644
                                  · linarith only [h1016, h1606, h1643, h1644, hc01, hc23, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1646 | h1646
                                    · linarith only [h1016, h1261, h1264, h1601, h1605, h1606, h1643, h1646, hc01, hc12, hlam, hphi]
                                    · rcases h0bigk with h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h0, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h726, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1016, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1148, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h0, h1261, h1643, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1648_1, u2ehi3]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h0, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1648_1, u2ehi3]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1264, h1605, hc01, hc13, hlam, hphi, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1261, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1262, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1648_1, u2ehi3]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1264, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1016, hc01, hc14, hlam, hphi, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1262, hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1016, h1606, hc03, hc45, hlam, hphi, ht34, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1511, hlam, p1648_0]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1264, h1601, h1605, hc01, hc12, hlam, hphi, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1263, hlam, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1261, h1264, h1601, h1605, h1643, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1648_1, u2ehi3]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [h1264, h1601, h1605, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1648_1]
                                      · obtain ⟨p1648_0, p1648_1, p1648_2, p1648_3⟩ := h1648c
                                        linarith only [hlam, p1648_0]
                                · linarith only [h1604, h1606, h1643, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1675 | h1675
                              · linarith only [h1262, h1511, h1604, h1605, h1675, hc35, hlam, hphi, ht23, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1677 | h1677
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1678 | h1678
                                  · linarith only [h1016, h1675, h1677, h1678, hc01, hc23, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1680 | h1680
                                    · linarith only [h1016, h1261, h1262, h1605, h1675, h1677, h1680, h726, hc35, hlam, hphi, ht23, u2ehi3]
                                    · rcases h0bigk with h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c | h1682c
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h0, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h726, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1016, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1148, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h0, h1261, h1677, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h0, h1262, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1682_1, u2ehi3]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h0, h1148, hc01, hc12, hlam, hphi, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1605, h1680, h726, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1261, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1262, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1682_1, u2ehi3]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1264, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1016, hc01, hc14, hlam, hphi, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1262, hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1016, h1604, h1605, h1680, hc03, hc45, hlam, hphi, ht34, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1511, hlam, p1682_0]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1148, h1605, h1680, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1263, hlam, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1148, h1261, h1605, h1677, h1680, hc45, hlam, hphi, ht23, ht34, p1682_1, u2ehi3]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [h1148, h1605, h1680, hc04, hc45, hlam, hphi, p1682_1]
                                      · obtain ⟨p1682_0, p1682_1, p1682_2, p1682_3⟩ := h1682c
                                        linarith only [hlam, p1682_0]
                                · linarith only [h1604, h1605, h1677, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1709 | h1709
                            · linarith only [h1261, h1264, h1604, h1709, hc34, hlam, hphi, ht23, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1711 | h1711
                              · linarith only [h1262, h1511, h1604, h1711, hc34, hlam, hphi, ht23, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1713 | h1713
                                · linarith only [h1261, h1604, h1713, h726, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1715 | h1715
                                  · linarith only [h1604, h1711, h1715, h726, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1717 | h1717
                                    · linarith only [h1016, h1262, h1711, h1717, hc34, hlam, hphi, ht23, u2ehi3]
                                    · linarith only [h1604, h1717, h726, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h1263, h1603, hlam]
                      · linarith only [h0, h1263, h1602, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h1263, h1601, hc23, hlam, hphi, u2ehi4]
              · linarith only [h1261, h1263, hc25, hlam, hphi, u2ehi2]
            · linarith only [h1261, h1262, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1725 | h1725
            · linarith only [h1261, h1725, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1727 | h1727
              · linarith only [h1261, h1727, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1729 | h1729
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1730 | h1730
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1731 | h1731
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1732 | h1732
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1733 | h1733
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1734 | h1734
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1735 | h1735
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1736 | h1736
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1737 | h1737
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1738 | h1738
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1739 | h1739
                                    · rcases h0bigk with h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c | h1740c
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h0, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h726, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1016, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1148, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1727, h1731, h1737, h1738, hc01, hc12, hlam, hphi, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1261, hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1725, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1727, hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1261, h1731, hc01, hc12, hlam, hphi, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1261, h1731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1261, h1727, h1730, h1731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1261, h1727, h1731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1016, h1734, hc01, hc13, hlam, hphi, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1725, h1731, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1725, h1731, h1737, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1725, h1727, h1731, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1729, h1731, h726, hc01, hc12, hlam, hphi, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1727, h1731, h1737, h1738, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1740_1, u2ehi0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1729, hlam, p1740_0]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [h1730, hlam, p1740_1]
                                      · obtain ⟨p1740_0, p1740_1, p1740_2, p1740_3⟩ := h1740c
                                        linarith only [hlam, p1740_0]
                                    · rcases h0bigk with h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c | h1766c
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h0, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h726, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1016, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1148, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1261, hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1725, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1727, hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1261, h1731, hc01, hc12, hlam, hphi, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1261, h1731, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1766_1, u2ehi0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1261, h1731, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1261, h1731, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1016, h1731, h1734, hc01, hc12, hlam, hphi, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1725, h1731, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1766_1, u2ehi0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1725, h1731, h1737, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1725, h1727, h1731, h1737, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1766_1, u2ehi0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1729, h1731, h726, hc01, hc12, hlam, hphi, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1727, h1731, h1737, h1738, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1766_1, u2ehi0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1729, hlam, p1766_0]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [h1730, hlam, p1766_1]
                                      · obtain ⟨p1766_0, p1766_1, p1766_2, p1766_3⟩ := h1766c
                                        linarith only [hlam, p1766_0]
                                  · linarith only [h1725, h1738, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h1261, h1737, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1016, h1725, h1730, h1732, h1736, hc01, hc12, hlam, hphi]
                            · linarith only [h1729, h1735, h726, hlam]
                          · linarith only [h1261, h1731, h1734, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1732, h1733, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h1261, h1731, h1732, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1799 | h1799
                      · linarith only [h1731, h1799, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1801 | h1801
                        · linarith only [h1731, h1801, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1803 | h1803
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1804 | h1804
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1805 | h1805
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1806 | h1806
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1807 | h1807
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1808 | h1808
                                    · rcases h0bigk with h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c | h1809c
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h0, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h726, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1148, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h0, h1801, h1806, h1807, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1261, hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1725, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1727, hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1731, h726, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1731, h726, hc23, hlam, hphi, p1809_1, u2ehi0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, h1731, h726, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1727, h1731, h726, hc23, hlam, hphi, p1809_1, u2ehi0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, h1731, h1803, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, h1731, h1803, hc23, hlam, hphi, p1809_1, u2ehi0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, h1731, h1803, h726, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1016, h1727, h1731, h1803, hc23, hlam, hphi, p1809_1, u2ehi0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1729, h1731, h726, hc01, hc23, hlam, hphi, ht12, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1148, h1731, h1803, h1805, hc23, hlam, hphi, p1809_1, u2ehi0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1729, hlam, p1809_0]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [h1730, hlam, p1809_1]
                                      · obtain ⟨p1809_0, p1809_1, p1809_2, p1809_3⟩ := h1809c
                                        linarith only [hlam, p1809_0]
                                    · rcases h0bigk with h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c | h1835c
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h0, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h726, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1148, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h0, h1801, h1806, h1807, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1261, hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1725, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1727, hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1731, h726, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1731, h726, hc23, hlam, hphi, p1835_1, u2ehi0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, h1731, h726, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1148, h1731, h726, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, h1731, h1803, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, h1731, h1803, hc23, hlam, hphi, p1835_1, u2ehi0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, h1731, h1803, h726, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1016, h1727, h1731, h1803, hc23, hlam, hphi, p1835_1, u2ehi0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1729, h1731, h726, hc01, hc23, hlam, hphi, ht12, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1148, h1731, h1803, h1805, hc23, hlam, hphi, p1835_1, u2ehi0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1729, hlam, p1835_0]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [h1730, hlam, p1835_1]
                                      · obtain ⟨p1835_0, p1835_1, p1835_2, p1835_3⟩ := h1835c
                                        linarith only [hlam, p1835_0]
                                  · linarith only [h1725, h1807, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h0, h1731, h1806, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h1016, h1730, h1805, hlam]
                            · linarith only [h1729, h1804, h726, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1865 | h1865
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1866 | h1866
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1867 | h1867
                                · linarith only [h1803, h1867, h726, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1261, h1867, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1016, h1730, h1866, hlam]
                            · linarith only [h1729, h1865, h726, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1872 | h1872
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1873 | h1873
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1874 | h1874
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1875 | h1875
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1876 | h1876
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1877 | h1877
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1878 | h1878
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1879 | h1879
                                  · linarith only [h1725, h1730, h1872, h1878, h1879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                  · linarith only [h1725, h1879, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h1261, h1878, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1725, h1873, h1877, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                            · linarith only [h1729, h1876, h726, hlam]
                          · linarith only [h1261, h1872, h1875, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1261, h1872, h1874, hc25, hlam, hphi, u2ehi0]
                      · linarith only [h1261, h1872, h1873, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1888 | h1888
                      · linarith only [h1872, h1888, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1890 | h1890
                        · linarith only [h1872, h1890, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1892 | h1892
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1893 | h1893
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1894 | h1894
                              · linarith only [h1725, h1730, h1888, h1894, hc24, hlam, hphi, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1896 | h1896
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1897 | h1897
                                  · linarith only [h1888, h1894, h1896, h1897, hc23, hlam, hphi, u2ehi1]
                                  · linarith only [h1725, h1897, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h1261, h1896, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1729, h1893, h726, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1902 | h1902
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1903 | h1903
                              · linarith only [h1725, h1730, h1888, h1903, hc24, hlam, hphi, u2ehi0]
                              · linarith only [h1892, h1902, h1903, hlam]
                            · linarith only [h1729, h1902, h726, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1907 | h1907
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1908 | h1908
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1909 | h1909
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1910 | h1910
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1911 | h1911
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1912 | h1912
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1913 | h1913
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1914 | h1914
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1915 | h1915
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1916 | h1916
                                    · linarith only [h1729, h1908, h1914, h1916, h726, hc01, hc12, hlam, hphi]
                                    · linarith only [h1261, h1725, h1729, h1907, h1908, h1914, h1916, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                  · linarith only [h1725, h1915, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h1261, h1914, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1016, h1725, h1907, h1909, h1913, hc01, hc12, hlam, hphi]
                            · linarith only [h1261, h1908, h1912, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1261, h1908, h1911, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1909, h1910, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h1261, h1908, h1909, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1926 | h1926
                      · linarith only [h1908, h1926, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1928 | h1928
                        · linarith only [h1908, h1928, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1930 | h1930
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1931 | h1931
                            · linarith only [h1261, h1729, h1908, h1931, hc23, hlam, hphi, u2ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1933 | h1933
                              · linarith only [h1930, h1931, h1933, hlam]
                              · linarith only [h1016, h1907, h1933, hlam]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1936 | h1936
                            · linarith only [h1261, h1729, h1908, h1936, hc23, hlam, hphi, u2ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1938 | h1938
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1939 | h1939
                                · linarith only [h1930, h1939, h726, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1261, h1939, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1016, h1907, h1938, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1943 | h1943
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1944 | h1944
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1945 | h1945
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1946 | h1946
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1947 | h1947
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1948 | h1948
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1949 | h1949
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1950 | h1950
                                  · linarith only [h1725, h1907, h1943, h1949, h1950, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                  · linarith only [h1725, h1946, h1948, h1950, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                · linarith only [h1261, h1949, hc34, hlam, hphi, ht23, u2ehi0]
                              · linarith only [h1725, h1944, h1948, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                            · linarith only [h1261, h1943, h1947, hc35, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h1261, h1943, h1946, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1261, h1943, h1945, hc25, hlam, hphi, u2ehi0]
                      · linarith only [h1261, h1943, h1944, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1959 | h1959
                      · linarith only [h1943, h1959, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1961 | h1961
                        · linarith only [h1943, h1961, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1963 | h1963
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1964 | h1964
                            · linarith only [h1261, h1729, h1943, h1964, hc23, hlam, hphi, u2ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1966 | h1966
                              · linarith only [h1725, h1907, h1963, h1964, h1966, hc35, hlam, hphi, ht23, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1968 | h1968
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1969 | h1969
                                  · linarith only [h1959, h1966, h1969, hc24, hlam, hphi, u2ehi1]
                                  · linarith only [h1725, h1969, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                                · linarith only [h1963, h1964, h1968, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1973 | h1973
                            · linarith only [h1261, h1729, h1963, h1973, hc34, hlam, hphi, ht23, u2ehi0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1975 | h1975
                              · linarith only [h1725, h1907, h1963, h1975, hc34, hlam, hphi, ht23, u2ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1977 | h1977
                                · linarith only [h1963, h1977, h726, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1261, h1977, hc34, hlam, hphi, ht23, u2ehi0]

theorem n7l_sAA2_M_LR_H_L_L_0 (m : N7Model)
    (h0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (h1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (h2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  obtain ⟨_, _, h0ehi, _⟩ := h0
  obtain ⟨h1elo, _, _⟩ := h1
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  linarith only [hlam, hphi, ht01, u0ehi5, u1elo0]

end R2N4
