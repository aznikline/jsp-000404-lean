import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_M_IR_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases h0bigk with h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c | h3c
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi2]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, h2, hc02, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, h2, hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc01, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3_1, u2ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hc03, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hc03, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3_1, u2ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hc03, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, hc03, hlam, hphi, p3_1, u0ehi4]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3_1, u2ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, h2, hc03, hlam, hphi, p3_1, u0ehi1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h1, h2, hlam, p3_1]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [h2, hlam, p3_0]
        · have p3_0 := h3c.1
          have p3_1 := h3c.2.1
          have p3_2 := h3c.2.2.1
          have p3_3 := h3c.2.2.2
          linarith only [hlam, p3_0]
      · rcases h0bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hlam, p29_0]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hc01, hlam, hphi, p29_1, u0ehi1]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hc01, hlam, hphi, p29_1, u0ehi2]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hc01, hlam, hphi, p29_1, u0ehi3]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hc01, hlam, hphi, p29_1, u0ehi4]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h0, hlam, p29_1]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hlam, p29_0]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h1, hc02, hlam, hphi, p29_1, u0ehi3]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h0, hc01, hlam, hphi, p29_1, u0ehi3]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h0, h2, hc01, hlam, hphi, p29_1, u0ehi3]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hc03, hlam, hphi, p29_1, u0ehi0]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hc03, hlam, hphi, p29_1, u0ehi1]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hlam, p29_0]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hc03, hlam, hphi, p29_1, u0ehi3]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h2, hc03, hlam, hphi, p29_1, u0ehi3]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi1]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h2, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p29_1, u0ehi1]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h1, hlam, p29_1]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hlam, p29_0]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h2, hlam, p29_1]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h0, h2, hc45, hlam, hphi, ht23, ht34, p29_1, u2ehi1]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h2, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p29_1, u0ehi1]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h2, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p29_1, u0ehi2]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [h2, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p29_1, u0ehi3]
        · have p29_0 := h29c.1
          have p29_1 := h29c.2.1
          have p29_2 := h29c.2.2.1
          have p29_3 := h29c.2.2.2
          linarith only [hlam, p29_0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h55 | h55
      · rcases h0bigk with h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c | h56c
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [hlam, p56_0]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [hc01, hlam, hphi, p56_1, u0ehi1]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [hc01, hlam, hphi, p56_1, u0ehi2]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h1, hc01, hlam, hphi, p56_1, u0ehi2]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [hc01, hlam, hphi, p56_1, u0ehi4]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h0, hlam, p56_1]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [hlam, p56_0]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [hc02, hlam, hphi, p56_1, u0ehi2]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h0, h1, hc01, hlam, hphi, p56_1, u0ehi2]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h0, hc01, hlam, hphi, p56_1, u0ehi4]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h0, h1, hc34, hlam, hphi, ht23, p56_1, u2ehi0]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h1, hc34, hlam, hphi, ht01, ht12, ht23, p56_1, u0ehi1]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [hlam, p56_0]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h1, hlam, p56_0]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h1, hc34, hlam, hphi, ht01, ht12, ht23, p56_1, u0ehi4]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p56_1, u2ehi1]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h1, hc34, hlam, hphi, ht01, ht12, ht23, p56_1, u0ehi1]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h1, hc34, hlam, hphi, ht01, ht12, ht23, p56_1, u0ehi2]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [hlam, p56_0]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h1, hc34, hlam, hphi, ht01, ht12, ht23, p56_1, u0ehi4]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p56_1, u2ehi1]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h1, h55, hc34, hlam, hphi, ht01, ht12, ht23, p56_1, u0ehi1]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h1, h55, hc34, hlam, hphi, ht01, ht12, ht23, p56_1, u0ehi2]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [h55, hlam, p56_0]
        · have p56_0 := h56c.1
          have p56_1 := h56c.2.1
          have p56_2 := h56c.2.2.1
          have p56_3 := h56c.2.2.2
          linarith only [hlam, p56_0]
      · rcases h0bigk with h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [hlam, p82_0]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [hc01, hlam, hphi, p82_1, u0ehi1]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [hc01, hlam, hphi, p82_1, u0ehi2]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [hc01, hlam, hphi, p82_1, u0ehi3]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [hc01, hlam, hphi, p82_1, u0ehi4]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h0, hlam, p82_1]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [hlam, p82_0]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [hc02, hlam, hphi, p82_1, u0ehi2]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h0, h1, hc01, hlam, hphi, p82_1, u0ehi2]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h0, h1, h55, hc01, hlam, hphi, p82_1, u0ehi2]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [hc03, hlam, hphi, p82_1, u0ehi0]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h1, h55, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p82_1, u0ehi1]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [hlam, p82_0]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h1, hlam, p82_0]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h1, h55, hlam, p82_1]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h0, h55, hc45, hlam, hphi, ht23, ht34, p82_1, u2ehi1]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h55, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p82_1, u0ehi1]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h55, hc03, hc45, hlam, hphi, ht34, p82_1]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [hlam, p82_0]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h55, hlam, p82_1]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p82_1, u2ehi1]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h55, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p82_1, u0ehi1]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h55, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p82_1, u0ehi2]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [h1, h55, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p82_1, u0ehi2]
        · have p82_0 := h82c.1
          have p82_1 := h82c.2.1
          have p82_2 := h82c.2.2.1
          have p82_3 := h82c.2.2.2
          linarith only [hlam, p82_0]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h108 | h108
    · rcases m.htr 0 4 5 (by decide) (by decide) with h109 | h109
      · rcases h0bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [hlam, p110_0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h0, hlam, p110_0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h108, h109, hc01, hlam, hphi, p110_1, u0ehi4]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h0, h109, hc12, hlam, hphi, ht01, p110_1, u0ehi4]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p110_1, u0ehi4]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p110_1, u0ehi0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [hlam, p110_0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h0, h108, h109, hc12, hlam, hphi, ht01, p110_1, u0ehi4]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h0, h109, hc12, hlam, hphi, ht01, p110_1, u0ehi4]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p110_1, u0ehi4]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [hc03, hlam, hphi, p110_1, u0ehi0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [hc03, hlam, hphi, p110_1, u0ehi1]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [hlam, p110_0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h109, hc03, hlam, hphi, p110_1, u0ehi4]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [hc03, hlam, hphi, p110_1, u0ehi4]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [hc04, hlam, hphi, p110_1, u0ehi0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h0, h108, hc03, hlam, hphi, p110_1, u0ehi0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h108, hlam, p110_1]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [hlam, p110_0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h108, hc03, hlam, hphi, p110_1, u0ehi4]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [hc05, hlam, hphi, p110_1, u0ehi0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h0, h108, h109, hc03, hlam, hphi, p110_1, u0ehi0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h108, h109, hlam, p110_1]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [h109, hlam, p110_0]
        · have p110_0 := h110c.1
          have p110_1 := h110c.2.1
          have p110_2 := h110c.2.2.1
          have p110_3 := h110c.2.2.2
          linarith only [hlam, p110_0]
      · rcases h0bigk with h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c | h136c
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [hlam, p136_0]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h0, hlam, p136_0]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [hc01, hlam, hphi, p136_1, u0ehi2]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p136_1, u0ehi3]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p136_1, u0ehi4]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p136_1, u0ehi0]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [hlam, p136_0]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h0, h108, hc12, hlam, hphi, ht01, p136_1, u0ehi3]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p136_1, u0ehi3]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h0, h109, hc12, hlam, hphi, ht01, p136_1, u0ehi3]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [hc03, hlam, hphi, p136_1, u0ehi0]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [hc03, hlam, hphi, p136_1, u0ehi1]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [hlam, p136_0]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [hc03, hlam, hphi, p136_1, u0ehi3]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h109, hc03, hlam, hphi, p136_1, u0ehi3]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [hc04, hlam, hphi, p136_1, u0ehi0]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h0, h109, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p136_1, u0ehi0]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h108, hlam, p136_1]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [hlam, p136_0]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h109, hlam, p136_1]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h109, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p136_1, u0ehi0]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h0, h109, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p136_1, u0ehi0]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h109, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p136_1, u0ehi2]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [h109, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p136_1, u0ehi3]
        · have p136_0 := h136c.1
          have p136_1 := h136c.2.1
          have p136_2 := h136c.2.2.1
          have p136_3 := h136c.2.2.2
          linarith only [hlam, p136_0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h162 | h162
      · rcases h0bigk with h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [hlam, p163_0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h0, hlam, p163_0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [hc01, hlam, hphi, p163_1, u0ehi2]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h0, h108, hc12, hlam, hphi, ht01, p163_1, u0ehi2]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p163_1, u0ehi4]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p163_1, u0ehi0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [hlam, p163_0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p163_1, u0ehi2]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h0, h108, hc12, hlam, hphi, ht01, p163_1, u0ehi2]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p163_1, u0ehi4]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [hc03, hlam, hphi, p163_1, u0ehi0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h108, hc34, hlam, hphi, ht23, p163_1, u2ehi0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [hlam, p163_0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h108, hlam, p163_0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h108, hc34, hlam, hphi, ht01, ht12, ht23, p163_1, u0ehi4]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h108, hc34, hlam, hphi, ht01, ht12, ht23, p163_1, u0ehi0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h0, h108, hc34, hlam, hphi, ht01, ht12, ht23, p163_1, u0ehi0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h108, hc34, hlam, hphi, ht01, ht12, ht23, p163_1, u0ehi2]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [hlam, p163_0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h108, hc34, hlam, hphi, ht01, ht12, ht23, p163_1, u0ehi4]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [hc05, hlam, hphi, p163_1, u0ehi0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h0, h108, h162, hc34, hlam, hphi, ht01, ht12, ht23, p163_1, u0ehi0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h108, h162, hc34, hlam, hphi, ht01, ht12, ht23, p163_1, u0ehi2]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [h162, hlam, p163_0]
        · have p163_0 := h163c.1
          have p163_1 := h163c.2.1
          have p163_2 := h163c.2.2.1
          have p163_3 := h163c.2.2.2
          linarith only [hlam, p163_0]
      · rcases h0bigk with h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [hlam, p189_0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h0, hlam, p189_0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [hc01, hlam, hphi, p189_1, u0ehi2]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p189_1, u0ehi3]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p189_1, u0ehi4]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p189_1, u0ehi0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [hlam, p189_0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h0, hc12, hlam, hphi, ht01, p189_1, u0ehi2]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h0, h108, hc12, hlam, hphi, ht01, p189_1, u0ehi2]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h0, h108, h162, hc12, hlam, hphi, ht01, p189_1, u0ehi2]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [hc03, hlam, hphi, p189_1, u0ehi0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h108, h162, hc45, hlam, hphi, ht23, ht34, p189_1, u2ehi0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [hlam, p189_0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h108, hlam, p189_0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h108, h162, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p189_1, u0ehi4]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h162, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p189_1, u0ehi0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h0, h162, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p189_1, u0ehi0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h162, hc03, hc45, hlam, hphi, ht34, p189_1]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [hlam, p189_0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h162, hlam, p189_1]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [hc05, hlam, hphi, p189_1, u0ehi0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h0, h162, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p189_1, u0ehi0]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h162, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p189_1, u0ehi2]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [h162, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p189_1, u0ehi3]
        · have p189_0 := h189c.1
          have p189_1 := h189c.2.1
          have p189_2 := h189c.2.2.1
          have p189_3 := h189c.2.2.2
          linarith only [hlam, p189_0]

theorem r1l7_20_12_14_M_LR_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h6, h9, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h0, h6, h7, h9, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h0, h12, h6, h7, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h16, h3, h7, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h15, h18, h6, h7, hlam]
                      · rcases h4bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          rcases p20_3 (m.d 0 4) (by simp) with h22 | h22
                          · rcases p20_3 (m.d 1 4) (by simp) with h23 | h23
                            · linarith only [h1, h23, hlam]
                            · rcases p20_3 (m.d 2 4) (by simp) with h25 | h25
                              · linarith only [h25, h3, hlam]
                              · rcases p20_3 (m.d 3 4) (by simp) with h27 | h27
                                · linarith only [h27, h4, hlam]
                                · rcases p20_3 (m.d 4 5) (by simp) with h29 | h29
                                  · linarith only [h29, h5, hlam]
                                  · linarith only [h29, h7, hlam]
                          · linarith only [h1, h22, hlam]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          rcases p20_3 (m.d 0 4) (by simp) with h33 | h33
                          · rcases p20_3 (m.d 1 4) (by simp) with h34 | h34
                            · linarith only [h1, h34, hlam]
                            · linarith only [h34, h6, hlam]
                          · linarith only [h3, h33, hlam]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          rcases p20_3 (m.d 0 4) (by simp) with h38 | h38
                          · rcases p20_3 (m.d 1 4) (by simp) with h39 | h39
                            · linarith only [h1, h39, hlam]
                            · linarith only [h15, h39, h6, hlam]
                          · linarith only [h38, h4, hlam]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h15, h2, h4, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h1, hlam, p20_1]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h15, h7, hc34, hc45, hlam, hphi, p20_1]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h2, h4, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h7, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h3, hlam, p20_1]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h6, hlam, p20_1]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h16, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h4, hlam, p20_1]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h2, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h15, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h18, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h5, hlam, p20_0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h2, h4, h5, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h15, h2, h4, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [h2, h4, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20_1, u2elo0]
                        · have p20_0 := h20c.1
                          have p20_1 := h20c.2.1
                          have p20_2 := h20c.2.2.1
                          have p20_3 := h20c.2.2.2
                          linarith only [hlam, p20_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                    · linarith only [h0, h6, h64, h7, hc15, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                      · linarith only [h15, h2, h4, h6, h66, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h15, h2, h4, h5, h66, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h3, h6, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
              · rcases m.htr 1 4 5 (by decide) (by decide) with h71 | h71
                · linarith only [h5, h71, hc14, hlam, hphi, ht01, u0ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h74 | h74
                    · linarith only [h5, h74, hlam, hphi, ht01, ht12, u0ehi8, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h76 | h76
                      · linarith only [h5, h76, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                      · rcases h4bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h5, hc14, hc45, hlam, hphi, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h5, hc24, hc45, hlam, hphi, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h5, hc34, hc45, hlam, hphi, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h5, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, hlam, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, hc24, hlam, hphi, ht0b, ht45, ht5b, p78_1, u0elo0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h0, h70, hc34, hlam, hphi, ht0b, ht45, ht5b, p78_1, u0elo0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h71, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h3, hlam, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h70, hlam, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p78_1, u2elo0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h74, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h4, hlam, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h2, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p78_1, u2elo0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h73, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h76, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p78_1, u0ehi8]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 4) (by simp) with h100 | h100
                          · linarith only [h100, h5, hlam]
                          · linarith only [h1, h100, hlam]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 4) (by simp) with h103 | h103
                          · linarith only [h103, h5, hlam]
                          · linarith only [h103, h3, hlam]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 4) (by simp) with h106 | h106
                          · linarith only [h106, h5, hlam]
                          · linarith only [h106, h4, hlam]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h110 | h110
                    · linarith only [h110, h5, h70, hc14, hlam, hphi, ht01, u0ehi8]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                      · linarith only [h112, h2, h4, h5, hlam, hphi, ht01, ht12, u0ehi8, u2elo0]
                      · rcases h4bigk with h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [hlam, p114_0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h5, hc14, hc45, hlam, hphi, p114_1]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h5, hc24, hc45, hlam, hphi, p114_1]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h5, h73, hc23, hc45, hlam, hphi, ht34, p114_1]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h5, hlam, p114_0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h1, hlam, p114_1]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [hlam, p114_0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h1, hc24, hlam, hphi, ht0b, ht45, ht5b, p114_1, u0elo0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h0, h70, h73, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p114_1, u0elo0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h71, hlam, p114_0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h3, hlam, p114_1]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h70, hlam, p114_1]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [hlam, p114_0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h73, hlam, p114_1]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h110, hlam, p114_0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h4, hlam, p114_1]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h2, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p114_1, u2elo0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h2, h4, h73, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p114_1, u2elo0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [hlam, p114_0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h112, hlam, p114_0]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p114_1, u0ehi8]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          rcases p114_3 (m.d 0 4) (by simp) with h136 | h136
                          · linarith only [h136, h5, hlam]
                          · linarith only [h1, h136, hlam]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          rcases p114_3 (m.d 0 4) (by simp) with h139 | h139
                          · linarith only [h139, h5, hlam]
                          · linarith only [h139, h3, hlam]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [h73, hc23, hc45, hlam, hphi, ht34, p114_1]
                        · have p114_0 := h114c.1
                          have p114_1 := h114c.2.1
                          have p114_2 := h114c.2.2.1
                          have p114_3 := h114c.2.2.2
                          linarith only [hlam, p114_0]
              · linarith only [h3, h70, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h145 | h145
            · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
              · rcases m.htr 1 4 5 (by decide) (by decide) with h147 | h147
                · rcases m.htr 2 3 4 (by decide) (by decide) with h148 | h148
                  · linarith only [h148, h4, hlam, hphi, ht01, ht12, u0ehi7, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                    · linarith only [h0, h146, h150, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h1, h147, h150, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                  · linarith only [h153, h4, hlam, hphi, ht01, ht12, u0ehi7, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h155 | h155
                    · linarith only [h146, h147, h155, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
                      · rcases h4bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [hlam, p158_0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          rcases p158_3 (m.d 0 4) (by simp) with h160 | h160
                          · rcases p158_3 (m.d 1 4) (by simp) with h161 | h161
                            · linarith only [h1, h161, hlam]
                            · rcases p158_3 (m.d 2 4) (by simp) with h163 | h163
                              · linarith only [h163, h3, hlam]
                              · rcases p158_3 (m.d 3 4) (by simp) with h165 | h165
                                · rcases p158_3 (m.d 4 5) (by simp) with h166 | h166
                                  · linarith only [h145, h166, hlam]
                                  · linarith only [h147, h166, hlam]
                                · linarith only [h145, h147, h165, h4, hlam, hphi, u0ehi7, u0elo3]
                          · linarith only [h1, h160, hlam]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          rcases p158_3 (m.d 0 4) (by simp) with h171 | h171
                          · rcases p158_3 (m.d 1 4) (by simp) with h172 | h172
                            · linarith only [h1, h172, hlam]
                            · linarith only [h146, h172, hlam]
                          · linarith only [h171, h3, hlam]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h4, hlam, p158_0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h147, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p158_1, u2elo0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h1, hlam, p158_1]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [hlam, p158_0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h147, h153, h157, hc23, hc35, hlam, hphi, p158_1]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h145, h147, h3, h4, hlam, hphi, ht01, ht12, p158_1, u0ehi7, u2elo0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h147, hlam, p158_0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h3, hlam, p158_1]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h146, hlam, p158_1]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [hlam, p158_0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h153, hlam, p158_1]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h155, hlam, p158_0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h145, h147, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p158_1]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          rcases p158_3 (m.d 0 4) (by simp) with h189 | h189
                          · linarith only [h189, h4, hlam]
                          · linarith only [h1, h189, hlam]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          rcases p158_3 (m.d 0 4) (by simp) with h192 | h192
                          · linarith only [h192, h4, hlam]
                          · linarith only [h192, h3, hlam]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [hlam, p158_0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h146, h147, h153, hc23, hc34, hlam, hphi, p158_1]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h145, hlam, p158_0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h145, h146, h153, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p158_1, u0elo3]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h145, h153, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p158_1, u2elo0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [h157, hlam, p158_0]
                        · have p158_0 := h158c.1
                          have p158_1 := h158c.2.1
                          have p158_2 := h158c.2.2.1
                          have p158_3 := h158c.2.2.2
                          linarith only [hlam, p158_0]
                      · linarith only [h145, h157, h3, h4, hlam, hphi, ht01, ht12, u0ehi7, u2elo0]
              · linarith only [h146, h3, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h204 | h204
              · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
                · linarith only [h145, h205, hc14, hlam, hphi, ht01, u0ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h207 | h207
                  · linarith only [h207, h4, hlam, hphi, ht01, ht12, u0ehi7, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h209 | h209
                    · linarith only [h145, h209, h4, hlam, hphi, ht01, ht12, u0ehi7, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h211 | h211
                      · linarith only [h145, h211, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                      · linarith only [h211, h4, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h204, h3, hc12, hlam, hphi, u2elo0]
        · linarith only [h3, hlam, hphi, ht01, ht12, u0ehi6, u2elo3]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h217 | h217
      · rcases m.htr 0 2 4 (by decide) (by decide) with h218 | h218
        · linarith only [h0, h1, h218, hlam]
        · linarith only [h218, hlam, hphi, ht01, ht12, u0ehi6, u2elo3]
      · linarith only [h217, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem r1l7_21_15_H_L_L_I (m : N7Model)
    (hb1 : CMSig2_7_H_L m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                    · linarith only [h1, h10, h8, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h0, h10, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h1, h13, h15, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h0, h15, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
                · linarith only [h18, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                  · linarith only [h0, h20, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h1, h20, h22, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h0, h22, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h25 | h25
              · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                  · linarith only [h0, h27, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                    · linarith only [h1, h27, h29, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h0, h29, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · linarith only [h25, h26, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h33 | h33
                · rcases m.htr 1 2 3 (by decide) (by decide) with h34 | h34
                  · linarith only [h0, h34, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
                    · linarith only [h1, h34, h36, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h0, h36, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                  · linarith only [h0, h39, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
                    · linarith only [h1, h39, h41, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h0, h4, h41, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h44 | h44
            · rcases m.htr 0 3 5 (by decide) (by decide) with h45 | h45
              · rcases m.htr 0 4 5 (by decide) (by decide) with h46 | h46
                · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
                  · linarith only [h0, h47, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
                    · linarith only [h1, h4, h47, h49, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
                      · linarith only [h1, h51, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h44, h51, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                  · linarith only [h0, h54, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h56 | h56
                    · linarith only [h0, h4, h56, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                      · linarith only [h1, h58, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h1, h44, h54, h58, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h61 | h61
                · linarith only [h44, h45, h61, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h63 | h63
                  · linarith only [h0, h63, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                    · linarith only [h0, h4, h65, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
                      · linarith only [h1, h67, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h3, h44, h45, h63, h67, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h70 | h70
              · rcases m.htr 0 4 5 (by decide) (by decide) with h71 | h71
                · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
                  · linarith only [h0, h72, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h74 | h74
                    · linarith only [h0, h4, h74, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h76 | h76
                      · linarith only [h1, h44, h76, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                        · linarith only [h2, h76, h78, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h44, h70, h72, h78, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h44, h70, h71, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h82 | h82
                · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
                  · linarith only [h0, h83, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h85 | h85
                    · linarith only [h0, h4, h85, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h87 | h87
                      · linarith only [h1, h87, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                        · linarith only [h2, h70, h87, h89, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                          · linarith only [h2, h91, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h2, h82, h83, h87, h91, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                  · linarith only [h0, h94, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                    · linarith only [h1, h94, h96, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                      · linarith only [h1, h44, h98, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                        · linarith only [h1, h100, h70, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                          · linarith only [h102, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                                  · linarith only [h104, h107, h2, h82, h94, h98, hc12, hc23, hlam, hphi]
                                  · linarith only [h1, h104, h106, h107, h44, h94, hc12, hc23, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h110 | h110
                                  · linarith only [h0, h104, h106, h110, h4, hc12, hc23, hlam, hphi]
                                  · rcases h5bigk with h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c | h112c
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [hlam, p112_0]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h102, h3, h94, h98, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p112_1, u1elo0]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h4, hlam, p112_0]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h70, hlam, p112_1]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h82, hlam, p112_1]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h3, hlam, p112_0]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [hlam, p112_0]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h96, hlam, p112_0]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h100, hlam, p112_1]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h102, hlam, p112_1]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      rcases p112_3 (m.d 0 5) (by simp) with h123 | h123
                                      · linarith only [h123, h4, hlam]
                                      · rcases p112_3 (m.d 1 5) (by simp) with h125 | h125
                                        · linarith only [h125, h96, hlam]
                                        · rcases p112_3 (m.d 2 5) (by simp) with h127 | h127
                                          · rcases p112_3 (m.d 3 5) (by simp) with h128 | h128
                                            · linarith only [h105, h128, hlam]
                                            · linarith only [h128, h70, hlam]
                                          · linarith only [h127, h4, hlam]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      rcases p112_3 (m.d 0 5) (by simp) with h132 | h132
                                      · linarith only [h132, h4, hlam]
                                      · linarith only [h132, h3, hlam]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [hlam, p112_0]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h1, h106, h110, h44, h94, hc12, hc45, hlam, hphi, ht23, ht34, p112_1]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h106, hlam, p112_1]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h102, h105, h3, h94, h98, hc12, hc23, hlam, hphi, p112_1]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h102, h105, h94, h98, hc12, hc23, hlam, hphi, p112_1]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h105, hlam, p112_0]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [hlam, p112_0]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h110, hlam, p112_1]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      rcases p112_3 (m.d 0 5) (by simp) with h143 | h143
                                      · linarith only [h143, h82, hlam]
                                      · rcases p112_3 (m.d 1 5) (by simp) with h145 | h145
                                        · linarith only [h102, h145, hlam]
                                        · rcases p112_3 (m.d 2 5) (by simp) with h147 | h147
                                          · linarith only [h106, h147, hlam]
                                          · linarith only [h147, h4, hlam]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      rcases p112_3 (m.d 0 5) (by simp) with h150 | h150
                                      · linarith only [h150, h82, hlam]
                                      · linarith only [h150, h3, hlam]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h0, h4, hc12, hc45, hlam, hphi, ht23, ht34, p112_1]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [h1, h70, h94, hc12, hc45, hlam, hphi, ht23, ht34, p112_1]
                                    · have p112_0 := h112c.1
                                      have p112_1 := h112c.2.1
                                      have p112_2 := h112c.2.2.1
                                      have p112_3 := h112c.2.2.2
                                      linarith only [hlam, p112_0]
                              · linarith only [h1, h104, h105, h44, h94, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h157 | h157
                              · linarith only [h1, h104, h157, h70, h94, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h159 | h159
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h160 | h160
                                  · rcases h5bigk with h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [hlam, p161_0]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h102, h3, h94, h98, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p161_1, u1elo0]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h4, hlam, p161_0]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h70, hlam, p161_1]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h82, hlam, p161_1]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h3, hlam, p161_0]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [hlam, p161_0]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h96, hlam, p161_0]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h100, hlam, p161_1]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h102, hlam, p161_1]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      rcases p161_3 (m.d 0 5) (by simp) with h172 | h172
                                      · linarith only [h172, h4, hlam]
                                      · rcases p161_3 (m.d 1 5) (by simp) with h174 | h174
                                        · linarith only [h174, h96, hlam]
                                        · rcases p161_3 (m.d 2 5) (by simp) with h176 | h176
                                          · rcases p161_3 (m.d 3 5) (by simp) with h177 | h177
                                            · rcases p161_3 (m.d 4 5) (by simp) with h178 | h178
                                              · linarith only [h159, h178, hlam]
                                              · linarith only [h178, h82, hlam]
                                            · linarith only [h177, h70, hlam]
                                          · linarith only [h176, h4, hlam]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      rcases p161_3 (m.d 0 5) (by simp) with h183 | h183
                                      · linarith only [h183, h4, hlam]
                                      · linarith only [h183, h3, hlam]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [hlam, p161_0]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h157, hlam, p161_1]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h157, h160, h2, h82, h94, h98, hc12, hc34, hlam, hphi, ht23, p161_1]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      rcases p161_3 (m.d 0 5) (by simp) with h189 | h189
                                      · linarith only [h189, h70, hlam]
                                      · rcases p161_3 (m.d 1 5) (by simp) with h191 | h191
                                        · linarith only [h100, h191, hlam]
                                        · rcases p161_3 (m.d 2 5) (by simp) with h193 | h193
                                          · linarith only [h157, h193, hlam]
                                          · linarith only [h193, h4, hlam]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      rcases p161_3 (m.d 0 5) (by simp) with h196 | h196
                                      · linarith only [h196, h70, hlam]
                                      · linarith only [h196, h3, hlam]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h0, h160, h4, hc12, hc34, hlam, hphi, ht23, p161_1]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [hlam, p161_0]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h160, h2, h82, h94, h98, hc12, hc34, hlam, hphi, ht23, p161_1]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h102, h104, h159, h3, h94, h98, hc12, hc34, hlam, hphi, ht23, p161_1]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h102, h104, h159, h94, h98, hc12, hc34, hlam, hphi, ht23, p161_1]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h159, hlam, p161_0]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [h160, hlam, p161_0]
                                    · have p161_0 := h161c.1
                                      have p161_1 := h161c.2.1
                                      have p161_2 := h161c.2.2.1
                                      have p161_3 := h161c.2.2.2
                                      linarith only [hlam, p161_0]
                                  · linarith only [h104, h159, h160, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                                  · linarith only [h104, h159, h208, h94, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h104, h208, h94, hc12, hc45, hlam, hphi, ht23, ht34]
        · linarith only [h3, hc01, hlam, hphi, u1elo4]
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
  · linarith only [h0, hc01, hlam, hphi, u1elo1]

end R2N4
