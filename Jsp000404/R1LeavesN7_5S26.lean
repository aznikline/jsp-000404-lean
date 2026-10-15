import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10516000 in
set_option maxHeartbeats 10516000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11844 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h15274 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15741 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h15990 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h15991 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  rcases m.htr 0 4 5 (by decide) (by decide) with h15992 | h15992
  · rcases m.htr 1 2 3 (by decide) (by decide) with h15993 | h15993
    · rcases m.htr 1 2 4 (by decide) (by decide) with h15994 | h15994
      · rcases m.htr 1 2 5 (by decide) (by decide) with h15995 | h15995
        · rcases m.htr 1 3 4 (by decide) (by decide) with h15996 | h15996
          · rcases m.htr 1 3 5 (by decide) (by decide) with h15997 | h15997
            · rcases m.htr 1 4 5 (by decide) (by decide) with h15998 | h15998
              · rcases m.htr 2 3 4 (by decide) (by decide) with h15999 | h15999
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16000 | h16000
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16001 | h16001
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16002 | h16002
                      · rcases h0bigk with h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c | h16003c
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [hlam, p16003_0]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h0, hlam, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h6310, hlam, p16003_0]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h9935, hlam, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h11282, hlam, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h15741, h15993, h15999, h16001, hc01, hc12, hlam, hphi, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [hlam, p16003_0]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h11844, hlam, p16003_0]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h15274, hlam, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h15741, hlam, p16003_0]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h11844, h15993, hc01, hc12, hlam, hphi, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h0, h11844, h15993, hc01, hc12, hlam, hphi, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [hlam, p16003_0]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h11844, h15993, h9935, hc01, hc12, hlam, hphi, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h0, h11844, h15741, h15993, hc01, hc12, hlam, hphi, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h15274, h15993, h15999, hc01, hc12, hlam, hphi, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h0, h15274, h15993, h15999, hc01, hc12, hlam, hphi, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h15990, hlam, p16003_0]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [hlam, p16003_0]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h11282, h15274, h15993, h15999, hc01, hc12, hlam, hphi, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h15741, h15993, h15999, h16001, hc01, hc12, hlam, hphi, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h0, h15741, h15993, h15999, h16001, hc01, hc12, hlam, hphi, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h15991, hlam, p16003_0]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [h15992, hlam, p16003_1]
                        · have p16003_0 := h16003c.1
                          have p16003_1 := h16003c.2.1
                          have p16003_2 := h16003c.2.2.1
                          have p16003_3 := h16003c.2.2.2
                          linarith only [hlam, p16003_0]
                      · rcases h0bigk with h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c | h16029c
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [hlam, p16029_0]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h0, hlam, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h6310, hlam, p16029_0]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h9935, hlam, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h11282, hlam, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h11844, h15993, hc01, hc12, hlam, hphi, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [hlam, p16029_0]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h11844, hlam, p16029_0]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h15274, hlam, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h15741, hlam, p16029_0]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h11844, h15993, hc01, hc12, hlam, hphi, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h0, h11844, h15993, hc01, hc12, hlam, hphi, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [hlam, p16029_0]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h11844, h15993, h9935, hc01, hc12, hlam, hphi, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h11282, h11844, h15993, hc01, hc12, hlam, hphi, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h15274, h15993, h15999, hc01, hc12, hlam, hphi, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h0, h15274, h15993, h15999, hc01, hc12, hlam, hphi, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h15990, hlam, p16029_0]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [hlam, p16029_0]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h0, h15274, h15741, h15993, h15999, hc01, hc12, hlam, hphi, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h15741, h15993, h15999, h16001, hc01, hc12, hlam, hphi, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h0, h15741, h15993, h15999, h16001, hc01, hc12, hlam, hphi, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h15991, hlam, p16029_0]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [h15992, hlam, p16029_1]
                        · have p16029_0 := h16029c.1
                          have p16029_1 := h16029c.2.1
                          have p16029_2 := h16029c.2.2.1
                          have p16029_3 := h16029c.2.2.2
                          linarith only [hlam, p16029_0]
                    · linarith only [h15274, h15992, h16001, hlam]
                  · linarith only [h11844, h15991, h16000, hlam]
                · linarith only [h11844, h15990, h15999, hlam]
              · linarith only [h15992, h15998, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
            · linarith only [h11844, h15991, h15993, h15997, hlam]
          · linarith only [h11844, h15990, h15993, h15996, hlam]
        · linarith only [h0, h11844, h15993, h15995, hc01, hc25, hlam, hphi, ht12]
      · linarith only [h0, h11844, h15993, h15994, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h16063 | h16063
      · linarith only [h0, h15274, h15993, h16063, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16065 | h16065
        · linarith only [h0, h15741, h15993, h16065, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16067 | h16067
          · rcases m.htr 1 3 5 (by decide) (by decide) with h16068 | h16068
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16069 | h16069
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16070 | h16070
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16071 | h16071
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16072 | h16072
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16073 | h16073
                      · rcases h0bigk with h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c | h16074c
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [hlam, p16074_0]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h0, hlam, p16074_1]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h6310, hlam, p16074_0]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h9935, hlam, p16074_1]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h11282, hlam, p16074_1]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h0, h16065, h16070, h16072, hc01, hc23, hlam, hphi, ht12, p16074_1]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [hlam, p16074_0]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h11844, hlam, p16074_0]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h15274, hlam, p16074_1]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h15741, hlam, p16074_0]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          rcases p16074_3 (m.d 0 1) (by simp) with h16085 | h16085
                          · linarith only [h16085, h6310, hlam]
                          · rcases p16074_3 (m.d 0 2) (by simp) with h16087 | h16087
                            · linarith only [h11844, h16087, hlam]
                            · linarith only [h0, h16087, hlam]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          rcases p16074_3 (m.d 0 1) (by simp) with h16090 | h16090
                          · linarith only [h16090, h6310, hlam]
                          · rcases p16074_3 (m.d 0 2) (by simp) with h16092 | h16092
                            · linarith only [h11844, h16092, hlam]
                            · rcases p16074_3 (m.d 0 3) (by simp) with h16094 | h16094
                              · rcases p16074_3 (m.d 0 4) (by simp) with h16095 | h16095
                                · linarith only [h15990, h16095, hlam]
                                · linarith only [h15274, h16095, hlam]
                              · linarith only [h11844, h16094, hlam]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [hlam, p16074_0]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h15990, h16073, hc45, hlam, hphi, ht0b, ht5b, p16074_1, u0elo2]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          rcases p16074_3 (m.d 0 1) (by simp) with h16101 | h16101
                          · linarith only [h16101, h6310, hlam]
                          · rcases p16074_3 (m.d 0 2) (by simp) with h16103 | h16103
                            · linarith only [h11844, h16103, hlam]
                            · rcases p16074_3 (m.d 0 3) (by simp) with h16105 | h16105
                              · rcases p16074_3 (m.d 0 4) (by simp) with h16106 | h16106
                                · linarith only [h15990, h16106, hlam]
                                · linarith only [h15992, h16106, hlam]
                              · linarith only [h15991, h16105, hlam]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          rcases p16074_3 (m.d 0 1) (by simp) with h16110 | h16110
                          · linarith only [h16110, h9935, hlam]
                          · rcases p16074_3 (m.d 0 2) (by simp) with h16112 | h16112
                            · linarith only [h15274, h16112, hlam]
                            · linarith only [h0, h16112, hlam]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          rcases p16074_3 (m.d 0 1) (by simp) with h16115 | h16115
                          · linarith only [h16115, h9935, hlam]
                          · rcases p16074_3 (m.d 0 2) (by simp) with h16117 | h16117
                            · linarith only [h15274, h16117, hlam]
                            · rcases p16074_3 (m.d 0 3) (by simp) with h16119 | h16119
                              · rcases p16074_3 (m.d 0 4) (by simp) with h16120 | h16120
                                · rcases p16074_3 (m.d 0 5) (by simp) with h16121 | h16121
                                  · linarith only [h15992, h16121, hlam]
                                  · linarith only [h15741, h16121, hlam]
                                · linarith only [h15274, h16120, hlam]
                              · linarith only [h11844, h16119, hlam]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h15990, hlam, p16074_0]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [hlam, p16074_0]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          rcases p16074_3 (m.d 0 1) (by simp) with h16128 | h16128
                          · linarith only [h16128, h9935, hlam]
                          · rcases p16074_3 (m.d 0 2) (by simp) with h16130 | h16130
                            · linarith only [h15274, h16130, hlam]
                            · rcases p16074_3 (m.d 0 3) (by simp) with h16132 | h16132
                              · rcases p16074_3 (m.d 0 4) (by simp) with h16133 | h16133
                                · rcases p16074_3 (m.d 0 5) (by simp) with h16134 | h16134
                                  · linarith only [h15992, h16134, hlam]
                                  · rcases h0emin with h16136 | h16136 | h16136 | h16136 | h16136
                                    · linarith only [h0, h15741, h16136, hlam, p16074_1, u0elo3]
                                    · linarith only [h15741, h16136, hlam, p16074_1, u0elo3]
                                    · rcases h1bigk with h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c | h16139c
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h0, hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h6310, hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h9935, hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h11282, hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h16065, h16070, h16072, hc01, hc23, hlam, hphi, ht12, p16139_1]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h15993, hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h16063, hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h16065, hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        rcases p16139_3 (m.d 0 1) (by simp) with h16150 | h16150
                                        · linarith only [h16150, hlam, p16139_0]
                                        · rcases p16139_3 (m.d 1 2) (by simp) with h16152 | h16152
                                          · linarith only [h15993, h16152, hlam]
                                          · linarith only [h0, h16152, hlam]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h0, h15993, hc01, hc23, hlam, hphi, ht12, p16139_1]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h0, h15741, h15993, h9935, hc01, hc23, hlam, hphi, ht12, p16074_1, p16139_1]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h0, h15993, h16065, hc01, hc23, hlam, hphi, ht12, p16139_1]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        rcases p16139_3 (m.d 0 1) (by simp) with h16159 | h16159
                                        · linarith only [h16159, hlam, p16139_0]
                                        · rcases p16139_3 (m.d 1 2) (by simp) with h16161 | h16161
                                          · linarith only [h16063, h16161, hlam]
                                          · linarith only [h0, h16161, hlam]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, p16139_1]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h16067, hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h0, h16063, h16065, h16070, hc01, hc23, hlam, hphi, ht12, p16139_1]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        rcases p16139_3 (m.d 0 1) (by simp) with h16168 | h16168
                                        · linarith only [h16168, hlam, p16139_0]
                                        · rcases p16139_3 (m.d 1 2) (by simp) with h16170 | h16170
                                          · linarith only [h16065, h16170, hlam]
                                          · linarith only [h0, h16170, hlam]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h0, hc01, hc15, hlam, hphi, p16139_1]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h16068, hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [h16069, hlam, p16139_0]
                                      · have p16139_0 := h16139c.1
                                        have p16139_1 := h16139c.2.1
                                        have p16139_2 := h16139c.2.2.1
                                        have p16139_3 := h16139c.2.2.2
                                        linarith only [hlam, p16139_0]
                                    · rcases h1bigk with h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c | h16177c
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h0, hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h6310, hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h9935, hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h11282, hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h15993, hc01, hc23, hlam, hphi, ht12, p16177_1]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h15993, hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h16063, hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h16065, hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        rcases p16177_3 (m.d 0 1) (by simp) with h16188 | h16188
                                        · linarith only [h16188, hlam, p16177_0]
                                        · rcases p16177_3 (m.d 1 2) (by simp) with h16190 | h16190
                                          · linarith only [h15993, h16190, hlam]
                                          · linarith only [h0, h16190, hlam]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h0, h15993, hc01, hc23, hlam, hphi, ht12, p16177_1]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h15993, h9935, hc01, hc23, hlam, hphi, ht12, p16177_1]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h11282, h15993, hc01, hc23, hlam, hphi, ht12, p16177_1]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        rcases p16177_3 (m.d 0 1) (by simp) with h16197 | h16197
                                        · linarith only [h16197, hlam, p16177_0]
                                        · rcases p16177_3 (m.d 1 2) (by simp) with h16199 | h16199
                                          · linarith only [h16063, h16199, hlam]
                                          · linarith only [h0, h16199, hlam]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, p16177_1]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h16067, hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h0, h16063, h16065, h16070, hc01, hc23, hlam, hphi, ht12, p16177_1]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        rcases p16177_3 (m.d 0 1) (by simp) with h16206 | h16206
                                        · linarith only [h16206, hlam, p16177_0]
                                        · rcases p16177_3 (m.d 1 2) (by simp) with h16208 | h16208
                                          · linarith only [h16065, h16208, hlam]
                                          · linarith only [h0, h16208, hlam]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h0, hc01, hc15, hlam, hphi, p16177_1]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h16068, hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [h16069, hlam, p16177_0]
                                      · have p16177_0 := h16177c.1
                                        have p16177_1 := h16177c.2.1
                                        have p16177_2 := h16177c.2.2.1
                                        have p16177_3 := h16177c.2.2.2
                                        linarith only [hlam, p16177_0]
                                    · linarith only [h15990, h16136, hlam, p16074_1, u0elo2]
                                · linarith only [h15992, h16133, hlam]
                              · linarith only [h15991, h16132, hlam]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          rcases p16074_3 (m.d 0 1) (by simp) with h16218 | h16218
                          · linarith only [h11282, h16218, hlam]
                          · rcases p16074_3 (m.d 0 2) (by simp) with h16220 | h16220
                            · linarith only [h15741, h16220, hlam]
                            · linarith only [h0, h16220, hlam]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          rcases p16074_3 (m.d 0 1) (by simp) with h16223 | h16223
                          · linarith only [h11282, h16223, hlam]
                          · rcases p16074_3 (m.d 0 2) (by simp) with h16225 | h16225
                            · linarith only [h15741, h16225, hlam]
                            · rcases p16074_3 (m.d 0 3) (by simp) with h16227 | h16227
                              · rcases p16074_3 (m.d 0 4) (by simp) with h16228 | h16228
                                · rcases p16074_3 (m.d 0 5) (by simp) with h16229 | h16229
                                  · rcases h0emin with h16230 | h16230 | h16230 | h16230 | h16230
                                    · linarith only [h0, h16230, hlam, p16074_1, u0elo4]
                                    · linarith only [h16230, hlam, p16074_1, u0elo4]
                                    · rcases h1bigk with h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c | h16233c
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h0, hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h6310, hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h9935, hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h11282, hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h15993, hc01, hc23, hlam, hphi, ht12, p16233_1]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h15993, hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h16063, hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h16065, hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        rcases p16233_3 (m.d 0 1) (by simp) with h16244 | h16244
                                        · linarith only [h16244, hlam, p16233_0]
                                        · rcases p16233_3 (m.d 1 2) (by simp) with h16246 | h16246
                                          · linarith only [h15993, h16246, hlam]
                                          · linarith only [h0, h16246, hlam]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h0, h15993, hc01, hc23, hlam, hphi, ht12, p16233_1]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h15993, h9935, hc01, hc23, hlam, hphi, ht12, p16233_1]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h11282, h15993, hc01, hc23, hlam, hphi, ht12, p16233_1]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        rcases p16233_3 (m.d 0 1) (by simp) with h16253 | h16253
                                        · linarith only [h16253, hlam, p16233_0]
                                        · rcases p16233_3 (m.d 1 2) (by simp) with h16255 | h16255
                                          · linarith only [h16063, h16255, hlam]
                                          · linarith only [h0, h16255, hlam]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, p16233_1]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h16067, hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h0, h11282, h16063, h16070, hc01, hc23, hlam, hphi, ht12, p16074_1, p16233_1]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        rcases p16233_3 (m.d 0 1) (by simp) with h16262 | h16262
                                        · linarith only [h16262, hlam, p16233_0]
                                        · rcases p16233_3 (m.d 1 2) (by simp) with h16264 | h16264
                                          · linarith only [h16065, h16264, hlam]
                                          · linarith only [h0, h16264, hlam]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h0, hc01, hc15, hlam, hphi, p16233_1]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h16068, hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [h16069, hlam, p16233_0]
                                      · have p16233_0 := h16233c.1
                                        have p16233_1 := h16233c.2.1
                                        have p16233_2 := h16233c.2.2.1
                                        have p16233_3 := h16233c.2.2.2
                                        linarith only [hlam, p16233_0]
                                    · rcases h1bigk with h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c | h16271c
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h0, hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h6310, hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h9935, hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h11282, hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h15993, hc01, hc23, hlam, hphi, ht12, p16271_1]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h15993, hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h16063, hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h16065, hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        rcases p16271_3 (m.d 0 1) (by simp) with h16282 | h16282
                                        · linarith only [h16282, hlam, p16271_0]
                                        · rcases p16271_3 (m.d 1 2) (by simp) with h16284 | h16284
                                          · linarith only [h15993, h16284, hlam]
                                          · linarith only [h0, h16284, hlam]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h0, h15993, hc01, hc23, hlam, hphi, ht12, p16271_1]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h15993, h9935, hc01, hc23, hlam, hphi, ht12, p16271_1]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h11282, h15993, hc01, hc23, hlam, hphi, ht12, p16271_1]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        rcases p16271_3 (m.d 0 1) (by simp) with h16291 | h16291
                                        · linarith only [h16291, hlam, p16271_0]
                                        · rcases p16271_3 (m.d 1 2) (by simp) with h16293 | h16293
                                          · linarith only [h16063, h16293, hlam]
                                          · linarith only [h0, h16293, hlam]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, p16271_1]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h16067, hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h0, h11282, h16063, h16070, hc01, hc23, hlam, hphi, ht12, p16074_1, p16271_1]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        rcases p16271_3 (m.d 0 1) (by simp) with h16300 | h16300
                                        · linarith only [h16300, hlam, p16271_0]
                                        · rcases p16271_3 (m.d 1 2) (by simp) with h16302 | h16302
                                          · linarith only [h16065, h16302, hlam]
                                          · linarith only [h0, h16302, hlam]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h0, hc01, hc15, hlam, hphi, p16271_1]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h16068, hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [h16069, hlam, p16271_0]
                                      · have p16271_0 := h16271c.1
                                        have p16271_1 := h16271c.2.1
                                        have p16271_2 := h16271c.2.2.1
                                        have p16271_3 := h16271c.2.2.2
                                        linarith only [hlam, p16271_0]
                                    · rcases h1bigk with h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h0, hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h6310, hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h9935, hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h11282, hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h15993, hc01, hc23, hlam, hphi, ht12, p16309_1]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h15993, hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h16063, hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h16065, hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        rcases p16309_3 (m.d 0 1) (by simp) with h16320 | h16320
                                        · linarith only [h16320, hlam, p16309_0]
                                        · rcases p16309_3 (m.d 1 2) (by simp) with h16322 | h16322
                                          · linarith only [h15993, h16322, hlam]
                                          · linarith only [h0, h16322, hlam]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h0, h15993, hc01, hc23, hlam, hphi, ht12, p16309_1]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h15993, h9935, hc01, hc23, hlam, hphi, ht12, p16309_1]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h11282, h15993, hc01, hc23, hlam, hphi, ht12, p16309_1]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        rcases p16309_3 (m.d 0 1) (by simp) with h16329 | h16329
                                        · linarith only [h16329, hlam, p16309_0]
                                        · rcases p16309_3 (m.d 1 2) (by simp) with h16331 | h16331
                                          · linarith only [h16063, h16331, hlam]
                                          · linarith only [h0, h16331, hlam]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, p16309_1]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h16067, hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h0, h11282, h16063, h16070, hc01, hc23, hlam, hphi, ht12, p16074_1, p16309_1]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        rcases p16309_3 (m.d 0 1) (by simp) with h16338 | h16338
                                        · linarith only [h16338, hlam, p16309_0]
                                        · rcases p16309_3 (m.d 1 2) (by simp) with h16340 | h16340
                                          · linarith only [h16065, h16340, hlam]
                                          · linarith only [h0, h16340, hlam]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h0, hc01, hc15, hlam, hphi, p16309_1]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h16068, hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [h16069, hlam, p16309_0]
                                      · have p16309_0 := h16309c.1
                                        have p16309_1 := h16309c.2.1
                                        have p16309_2 := h16309c.2.2.1
                                        have p16309_3 := h16309c.2.2.2
                                        linarith only [hlam, p16309_0]
                                  · linarith only [h15741, h16229, hlam]
                                · linarith only [h15274, h16228, hlam]
                              · linarith only [h11844, h16227, hlam]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h15991, hlam, p16074_0]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [h15992, hlam, p16074_1]
                        · have p16074_0 := h16074c.1
                          have p16074_1 := h16074c.2.1
                          have p16074_2 := h16074c.2.2.1
                          have p16074_3 := h16074c.2.2.2
                          linarith only [hlam, p16074_0]
                      · rcases h0bigk with h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c | h16353c
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [hlam, p16353_0]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h0, hlam, p16353_1]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h6310, hlam, p16353_0]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h9935, hlam, p16353_1]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h11282, hlam, p16353_1]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h11844, hc01, hc23, hlam, hphi, ht12, p16353_1]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [hlam, p16353_0]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h11844, hlam, p16353_0]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h15274, hlam, p16353_1]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h15741, hlam, p16353_0]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          rcases p16353_3 (m.d 0 1) (by simp) with h16364 | h16364
                          · linarith only [h16364, h6310, hlam]
                          · rcases p16353_3 (m.d 0 2) (by simp) with h16366 | h16366
                            · linarith only [h11844, h16366, hlam]
                            · linarith only [h0, h16366, hlam]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          rcases p16353_3 (m.d 0 1) (by simp) with h16369 | h16369
                          · linarith only [h16369, h6310, hlam]
                          · rcases p16353_3 (m.d 0 2) (by simp) with h16371 | h16371
                            · linarith only [h11844, h16371, hlam]
                            · rcases p16353_3 (m.d 0 3) (by simp) with h16373 | h16373
                              · rcases p16353_3 (m.d 0 4) (by simp) with h16374 | h16374
                                · linarith only [h15990, h16374, hlam]
                                · linarith only [h15274, h16374, hlam]
                              · linarith only [h11844, h16373, hlam]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [hlam, p16353_0]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h15992, h16073, hc34, hlam, hphi, ht0b, ht45, ht5b, p16353_1, u0elo2]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h15992, h16073, hc34, hlam, hphi, ht0b, ht45, ht5b, p16353_1, u0elo2]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          rcases p16353_3 (m.d 0 1) (by simp) with h16381 | h16381
                          · linarith only [h16381, h9935, hlam]
                          · rcases p16353_3 (m.d 0 2) (by simp) with h16383 | h16383
                            · linarith only [h15274, h16383, hlam]
                            · linarith only [h0, h16383, hlam]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          rcases p16353_3 (m.d 0 1) (by simp) with h16386 | h16386
                          · linarith only [h16386, h9935, hlam]
                          · rcases p16353_3 (m.d 0 2) (by simp) with h16388 | h16388
                            · linarith only [h15274, h16388, hlam]
                            · rcases p16353_3 (m.d 0 3) (by simp) with h16390 | h16390
                              · rcases p16353_3 (m.d 0 4) (by simp) with h16391 | h16391
                                · rcases p16353_3 (m.d 0 5) (by simp) with h16392 | h16392
                                  · linarith only [h15992, h16392, hlam]
                                  · linarith only [h15741, h16392, hlam]
                                · linarith only [h15274, h16391, hlam]
                              · linarith only [h11844, h16390, hlam]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h15990, hlam, p16353_0]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [hlam, p16353_0]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h15990, h15992, h16073, hc34, hlam, hphi, ht0b, ht45, ht5b, p16353_1, u0elo2]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          rcases p16353_3 (m.d 0 1) (by simp) with h16400 | h16400
                          · linarith only [h11282, h16400, hlam]
                          · rcases p16353_3 (m.d 0 2) (by simp) with h16402 | h16402
                            · linarith only [h15741, h16402, hlam]
                            · linarith only [h0, h16402, hlam]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          rcases p16353_3 (m.d 0 1) (by simp) with h16405 | h16405
                          · linarith only [h11282, h16405, hlam]
                          · rcases p16353_3 (m.d 0 2) (by simp) with h16407 | h16407
                            · linarith only [h15741, h16407, hlam]
                            · rcases p16353_3 (m.d 0 3) (by simp) with h16409 | h16409
                              · rcases p16353_3 (m.d 0 4) (by simp) with h16410 | h16410
                                · rcases p16353_3 (m.d 0 5) (by simp) with h16411 | h16411
                                  · rcases h0emin with h16412 | h16412 | h16412 | h16412 | h16412
                                    · linarith only [h0, h16065, h16070, h16072, h16412, hc23, hlam, ht01, ht12]
                                    · linarith only [h15990, h15992, h16412, hlam, p16353_1, u0elo2]
                                    · rcases h1bigk with h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h0, hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h6310, hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h9935, hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h11282, hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h16065, h16070, h16072, hc01, hc23, hlam, hphi, ht12, p16415_1]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h15993, hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h16063, hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h16065, hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        rcases p16415_3 (m.d 0 1) (by simp) with h16426 | h16426
                                        · linarith only [h16426, hlam, p16415_0]
                                        · rcases p16415_3 (m.d 1 2) (by simp) with h16428 | h16428
                                          · linarith only [h15993, h16428, hlam]
                                          · linarith only [h0, h16428, hlam]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h0, h15993, hc01, hc23, hlam, hphi, ht12, p16415_1]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h15993, h9935, hc01, hc23, hlam, hphi, ht12, p16415_1]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h11282, h15993, hc01, hc23, hlam, hphi, ht12, p16415_1]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        rcases p16415_3 (m.d 0 1) (by simp) with h16435 | h16435
                                        · linarith only [h16435, hlam, p16415_0]
                                        · rcases p16415_3 (m.d 1 2) (by simp) with h16437 | h16437
                                          · linarith only [h16063, h16437, hlam]
                                          · linarith only [h0, h16437, hlam]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, p16415_1]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h16067, hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h0, h11282, h16063, h16070, hc01, hc23, hlam, hphi, ht12, p16353_1, p16415_1]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        rcases p16415_3 (m.d 0 1) (by simp) with h16444 | h16444
                                        · linarith only [h16444, hlam, p16415_0]
                                        · rcases p16415_3 (m.d 1 2) (by simp) with h16446 | h16446
                                          · linarith only [h16065, h16446, hlam]
                                          · linarith only [h0, h16446, hlam]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h0, hc01, hc15, hlam, hphi, p16415_1]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h16068, hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [h16069, hlam, p16415_0]
                                      · have p16415_0 := h16415c.1
                                        have p16415_1 := h16415c.2.1
                                        have p16415_2 := h16415c.2.2.1
                                        have p16415_3 := h16415c.2.2.2
                                        linarith only [hlam, p16415_0]
                                    · rcases h1bigk with h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c | h16453c
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h0, hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h6310, hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h9935, hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h11282, hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h15993, hc01, hc23, hlam, hphi, ht12, p16453_1]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h15993, hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h16063, hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h16065, hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        rcases p16453_3 (m.d 0 1) (by simp) with h16464 | h16464
                                        · linarith only [h16464, hlam, p16453_0]
                                        · rcases p16453_3 (m.d 1 2) (by simp) with h16466 | h16466
                                          · linarith only [h15993, h16466, hlam]
                                          · linarith only [h0, h16466, hlam]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h0, h15993, hc01, hc23, hlam, hphi, ht12, p16453_1]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h15993, h9935, hc01, hc23, hlam, hphi, ht12, p16453_1]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h11282, h15993, hc01, hc23, hlam, hphi, ht12, p16453_1]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        rcases p16453_3 (m.d 0 1) (by simp) with h16473 | h16473
                                        · linarith only [h16473, hlam, p16453_0]
                                        · rcases p16453_3 (m.d 1 2) (by simp) with h16475 | h16475
                                          · linarith only [h16063, h16475, hlam]
                                          · linarith only [h0, h16475, hlam]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, p16453_1]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h16067, hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h0, h11282, h16063, h16070, hc01, hc23, hlam, hphi, ht12, p16353_1, p16453_1]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        rcases p16453_3 (m.d 0 1) (by simp) with h16482 | h16482
                                        · linarith only [h16482, hlam, p16453_0]
                                        · rcases p16453_3 (m.d 1 2) (by simp) with h16484 | h16484
                                          · linarith only [h16065, h16484, hlam]
                                          · linarith only [h0, h16484, hlam]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h0, hc01, hc15, hlam, hphi, p16453_1]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h16068, hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [h16069, hlam, p16453_0]
                                      · have p16453_0 := h16453c.1
                                        have p16453_1 := h16453c.2.1
                                        have p16453_2 := h16453c.2.2.1
                                        have p16453_3 := h16453c.2.2.2
                                        linarith only [hlam, p16453_0]
                                    · rcases h1bigk with h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c | h16491c
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h0, hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h6310, hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h9935, hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h11282, hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h15993, hc01, hc23, hlam, hphi, ht12, p16491_1]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h15993, hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h16063, hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h16065, hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        rcases p16491_3 (m.d 0 1) (by simp) with h16502 | h16502
                                        · linarith only [h16502, hlam, p16491_0]
                                        · rcases p16491_3 (m.d 1 2) (by simp) with h16504 | h16504
                                          · linarith only [h15993, h16504, hlam]
                                          · linarith only [h0, h16504, hlam]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h0, h15993, hc01, hc23, hlam, hphi, ht12, p16491_1]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h15993, h9935, hc01, hc23, hlam, hphi, ht12, p16491_1]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h11282, h15993, hc01, hc23, hlam, hphi, ht12, p16491_1]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        rcases p16491_3 (m.d 0 1) (by simp) with h16511 | h16511
                                        · linarith only [h16511, hlam, p16491_0]
                                        · rcases p16491_3 (m.d 1 2) (by simp) with h16513 | h16513
                                          · linarith only [h16063, h16513, hlam]
                                          · linarith only [h0, h16513, hlam]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, p16491_1]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h16067, hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h0, h11282, h16063, h16070, hc01, hc23, hlam, hphi, ht12, p16353_1, p16491_1]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        rcases p16491_3 (m.d 0 1) (by simp) with h16520 | h16520
                                        · linarith only [h16520, hlam, p16491_0]
                                        · rcases p16491_3 (m.d 1 2) (by simp) with h16522 | h16522
                                          · linarith only [h16065, h16522, hlam]
                                          · linarith only [h0, h16522, hlam]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h0, hc01, hc15, hlam, hphi, p16491_1]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h16068, hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [h16069, hlam, p16491_0]
                                      · have p16491_0 := h16491c.1
                                        have p16491_1 := h16491c.2.1
                                        have p16491_2 := h16491c.2.2.1
                                        have p16491_3 := h16491c.2.2.2
                                        linarith only [hlam, p16491_0]
                                  · linarith only [h15741, h16411, hlam]
                                · linarith only [h15274, h16410, hlam]
                              · linarith only [h11844, h16409, hlam]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h15991, hlam, p16353_0]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [h15992, hlam, p16353_1]
                        · have p16353_0 := h16353c.1
                          have p16353_1 := h16353c.2.1
                          have p16353_2 := h16353c.2.2.1
                          have p16353_3 := h16353c.2.2.2
                          linarith only [hlam, p16353_0]
                    · linarith only [h15992, h16063, h16072, h9935, hlam]
                  · linarith only [h15991, h15993, h16071, h6310, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h0, h15993, h16070, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h15992, h16069, h9935, hlam]
            · linarith only [h15991, h16068, h6310, hlam]
          · linarith only [h15990, h16067, h6310, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h16541 | h16541
    · rcases m.htr 1 2 4 (by decide) (by decide) with h16542 | h16542
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16543 | h16543
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16544 | h16544
          · rcases m.htr 1 3 5 (by decide) (by decide) with h16545 | h16545
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16546 | h16546
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16547 | h16547
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16548 | h16548
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16549 | h16549
                    · linarith only [h15992, h16542, h16549, h9935, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h15274, h16541, h16544, h16546, h16549, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11844, h15991, h16548, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h11844, h15990, h16547, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16554 | h16554
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16555 | h16555
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16556 | h16556
                    · linarith only [h16546, h16556, h9935, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16558 | h16558
                      · linarith only [h0, h15274, h15990, h16542, h16546, h16558, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · rcases h0bigk with h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c | h16560c
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [hlam, p16560_0]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h0, hlam, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h6310, hlam, p16560_0]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h9935, hlam, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h11282, hlam, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h15274, h16542, hc01, hc14, hlam, hphi, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [hlam, p16560_0]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h11844, hlam, p16560_0]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h15274, hlam, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h15741, hlam, p16560_0]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h11844, h16541, hc01, hc12, hlam, hphi, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h0, h11844, h16541, hc01, hc12, hlam, hphi, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [hlam, p16560_0]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h0, h11844, h15274, h16541, hc01, hc12, hlam, hphi, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h0, h11844, h15274, h15992, h16541, hc01, hc12, hlam, hphi, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h15992, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h0, h15992, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h15990, hlam, p16560_0]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [hlam, p16560_0]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h15992, hlam, p16560_0]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h15741, h16541, h16555, hc01, hc12, hlam, hphi, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h0, h15741, h16541, h16555, hc01, hc12, hlam, hphi, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h15991, hlam, p16560_0]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [h15741, h16541, h16555, h9935, hc01, hc12, hlam, hphi, p16560_1]
                        · have p16560_0 := h16560c.1
                          have p16560_1 := h16560c.2.1
                          have p16560_2 := h16560c.2.2.1
                          have p16560_3 := h16560c.2.2.2
                          linarith only [hlam, p16560_0]
                  · linarith only [h11844, h15991, h16555, hlam]
                · linarith only [h0, h11844, h15990, h16546, h16554, h9935, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h15991, h16545, h6310, hlam]
          · linarith only [h11844, h15990, h16541, h16544, hlam]
        · linarith only [h0, h11844, h16541, h16543, hc01, hc25, hlam, hphi, ht12]
      · linarith only [h0, h11844, h16541, h16542, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h16592 | h16592
      · linarith only [h0, h15274, h16541, h16592, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16594 | h16594
        · linarith only [h0, h15741, h16541, h16594, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16596 | h16596
          · rcases m.htr 1 3 5 (by decide) (by decide) with h16597 | h16597
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16598 | h16598
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16599 | h16599
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16600 | h16600
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16601 | h16601
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16602 | h16602
                      · linarith only [h0, h15274, h15990, h15992, h16602, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c | h16604c
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [hlam, p16604_0]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h0, hlam, p16604_1]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h6310, hlam, p16604_0]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h9935, hlam, p16604_1]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h11282, hlam, p16604_1]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h15274, h15992, h16598, hc01, hc14, hlam, hphi, p16604_1]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [hlam, p16604_0]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h11844, hlam, p16604_0]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h15274, hlam, p16604_1]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h15741, hlam, p16604_0]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          rcases p16604_3 (m.d 0 1) (by simp) with h16615 | h16615
                          · linarith only [h16615, h6310, hlam]
                          · rcases p16604_3 (m.d 0 2) (by simp) with h16617 | h16617
                            · linarith only [h11844, h16617, hlam]
                            · linarith only [h0, h16617, hlam]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          rcases p16604_3 (m.d 0 1) (by simp) with h16620 | h16620
                          · linarith only [h16620, h6310, hlam]
                          · rcases p16604_3 (m.d 0 2) (by simp) with h16622 | h16622
                            · linarith only [h11844, h16622, hlam]
                            · rcases p16604_3 (m.d 0 3) (by simp) with h16624 | h16624
                              · rcases p16604_3 (m.d 0 4) (by simp) with h16625 | h16625
                                · linarith only [h15990, h16625, hlam]
                                · linarith only [h15274, h16625, hlam]
                              · linarith only [h11844, h16624, hlam]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [hlam, p16604_0]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          rcases p16604_3 (m.d 0 1) (by simp) with h16630 | h16630
                          · linarith only [h16630, h6310, hlam]
                          · rcases p16604_3 (m.d 0 2) (by simp) with h16632 | h16632
                            · linarith only [h11844, h16632, hlam]
                            · rcases p16604_3 (m.d 0 3) (by simp) with h16634 | h16634
                              · rcases p16604_3 (m.d 0 4) (by simp) with h16635 | h16635
                                · linarith only [h15990, h16635, hlam]
                                · rcases p16604_3 (m.d 0 5) (by simp) with h16637 | h16637
                                  · linarith only [h15991, h16637, hlam]
                                  · linarith only [h15992, h16637, hlam]
                              · linarith only [h15990, h16634, hlam]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          rcases p16604_3 (m.d 0 1) (by simp) with h16641 | h16641
                          · linarith only [h16641, h6310, hlam]
                          · rcases p16604_3 (m.d 0 2) (by simp) with h16643 | h16643
                            · linarith only [h11844, h16643, hlam]
                            · rcases p16604_3 (m.d 0 3) (by simp) with h16645 | h16645
                              · rcases p16604_3 (m.d 0 4) (by simp) with h16646 | h16646
                                · linarith only [h15990, h16646, hlam]
                                · rcases p16604_3 (m.d 0 5) (by simp) with h16648 | h16648
                                  · linarith only [h15991, h16648, hlam]
                                  · rcases h0emin with h16650 | h16650 | h16650 | h16650 | h16650
                                    · linarith only [h0, h16594, h16599, h16601, h16650, hc23, hlam, ht01, ht12]
                                    · linarith only [h15274, h15992, h16650, hlam, p16604_1, u0elo2]
                                    · rcases h1bigk with h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c | h16653c
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h0, hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h6310, hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h9935, hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h11282, hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h16594, h16599, h16601, hc01, hc23, hlam, hphi, ht12, p16653_1]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h16541, hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h16592, hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h16594, hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        rcases p16653_3 (m.d 0 1) (by simp) with h16664 | h16664
                                        · linarith only [h16664, hlam, p16653_0]
                                        · rcases p16653_3 (m.d 1 2) (by simp) with h16666 | h16666
                                          · linarith only [h16541, h16666, hlam]
                                          · linarith only [h0, h16666, hlam]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h0, hc01, hc13, hlam, hphi, p16653_1]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h16541, h9935, hc01, hc23, hlam, hphi, ht12, p16653_1]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h0, h16541, h16594, hc01, hc23, hlam, hphi, ht12, p16653_1]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        rcases p16653_3 (m.d 0 1) (by simp) with h16673 | h16673
                                        · linarith only [h16673, hlam, p16653_0]
                                        · rcases p16653_3 (m.d 1 2) (by simp) with h16675 | h16675
                                          · linarith only [h16592, h16675, hlam]
                                          · linarith only [h0, h16675, hlam]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, p16653_1]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h16596, hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h0, h15274, h15992, h16592, h16598, h16599, hc01, hc23, hlam, hphi, ht12, p16653_1]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        rcases p16653_3 (m.d 0 1) (by simp) with h16682 | h16682
                                        · linarith only [h16682, hlam, p16653_0]
                                        · rcases p16653_3 (m.d 1 2) (by simp) with h16684 | h16684
                                          · linarith only [h16594, h16684, hlam]
                                          · linarith only [h0, h16684, hlam]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h0, hc01, hc15, hlam, hphi, p16653_1]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h16597, hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [h16598, hlam, p16653_0]
                                      · have p16653_0 := h16653c.1
                                        have p16653_1 := h16653c.2.1
                                        have p16653_2 := h16653c.2.2.1
                                        have p16653_3 := h16653c.2.2.2
                                        linarith only [hlam, p16653_0]
                                    · linarith only [h15992, h16650, hlam, p16604_1, u0elo2]
                                    · linarith only [h16650, hlam, p16604_1, u0elo2]
                              · linarith only [h15991, h16645, hlam]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h15992, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16604_1]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h0, h15992, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16604_1]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h15990, hlam, p16604_0]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [hlam, p16604_0]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h15992, hlam, p16604_0]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h15992, h16592, h16598, h16599, hc01, hc23, hlam, hphi, ht12, p16604_1]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h0, h15992, h16592, h16598, h16599, hc01, hc23, hlam, hphi, ht12, p16604_1]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h15991, hlam, p16604_0]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [h15992, h16592, h16598, h16599, h9935, hc01, hc23, hlam, hphi, ht12, p16604_1]
                        · have p16604_0 := h16604c.1
                          have p16604_1 := h16604c.2.1
                          have p16604_2 := h16604c.2.2.1
                          have p16604_3 := h16604c.2.2.2
                          linarith only [hlam, p16604_0]
                    · linarith only [h16592, h16598, h16601, hlam]
                  · linarith only [h15991, h15992, h16592, h16598, h16599, h16600, hc05, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h15990, h15992, h16541, h16596, h16598, h16599, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16707 | h16707
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16708 | h16708
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16709 | h16709
                    · linarith only [h0, h16592, h16598, h16709, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h16592, h16709, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h15991, h16541, h16708, h6310, hlam]
                · linarith only [h15990, h16541, h16707, h6310, hlam]
            · linarith only [h15991, h16597, h6310, hlam]
          · linarith only [h15990, h16596, h6310, hlam]

end R2N4
