import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_53S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h394 | h394
  · rcases m.htr 1 2 5 (by decide) (by decide) with h395 | h395
    · rcases m.htr 1 3 4 (by decide) (by decide) with h396 | h396
      · rcases m.htr 1 3 5 (by decide) (by decide) with h397 | h397
        · rcases m.htr 1 4 5 (by decide) (by decide) with h398 | h398
          · rcases h1bigk with h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c | h399c
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h394, h398, hc01, hlam, hphi, ht0b, ht5b, p399_1, u5ehi4]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h394, h398, h4, hc01, hlam, hphi, ht0b, ht5b, p399_1, u5ehi4]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h398, hc01, hlam, hphi, ht0b, ht5b, p399_1, u5ehi4]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p399_1, u5ehi1]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h0, hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h4, hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h398, hc12, hlam, hphi, ht01, ht0b, ht5b, p399_1, u5ehi4]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p399_1, u5ehi1]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h1, hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p399_1]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h1, h398, hc01, hlam, hphi, ht0b, ht5b, p399_1, u5ehi4]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h1, h395, hc01, hlam, hphi, ht0b, ht5b, p399_1, u5ehi2]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h2, hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h394, hlam, p399_1]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h396, hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h394, h395, hc12, hlam, hphi, ht01, ht0b, ht5b, p399_1, u5ehi2]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h3, hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h395, hlam, p399_1]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h397, hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [h398, hlam, p399_0]
            · have p399_0 := h399c.1
              have p399_1 := h399c.2.1
              have p399_2 := h399c.2.2.1
              have p399_3 := h399c.2.2.2
              linarith only [hlam, p399_0]
          · rcases h1bigk with h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h394, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p425_1]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h394, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p425_1]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              rcases p425_3 (m.d 0 1) (by simp) with h429 | h429
              · rcases p425_3 (m.d 1 2) (by simp) with h430 | h430
                · linarith only [h0, h430, hlam]
                · linarith only [h394, h430, hlam]
              · linarith only [h429, hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h395, hc01, hlam, hphi, ht0b, ht5b, p425_1, u5ehi2]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h0, hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h4, hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h0, h396, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p425_1]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h395, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p425_1, u5ehi2]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h1, hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p425_1]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h1, h396, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p425_1]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h1, h395, hc01, hlam, hphi, ht0b, ht5b, p425_1, u5ehi2]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h2, hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h394, hlam, p425_1]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h396, hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h398, hlam, p425_1]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h3, hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h395, hlam, p425_1]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h397, hlam, p425_0]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [h3, h396, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p425_1]
            · have p425_0 := h425c.1
              have p425_1 := h425c.2.1
              have p425_2 := h425c.2.2.1
              have p425_3 := h425c.2.2.2
              linarith only [hlam, p425_0]
        · linarith only [h395, h397, h4, hlam]
      · linarith only [h394, h396, h4, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h457 | h457
      · rcases m.htr 1 3 5 (by decide) (by decide) with h458 | h458
        · rcases m.htr 1 4 5 (by decide) (by decide) with h459 | h459
          · linarith only [h394, h395, h459, hlam]
          · rcases h1bigk with h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c | h461c
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h394, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p461_1]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h458, hc01, hlam, hphi, ht0b, ht5b, p461_1, u5ehi3]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              rcases p461_3 (m.d 0 1) (by simp) with h465 | h465
              · rcases p461_3 (m.d 1 2) (by simp) with h466 | h466
                · linarith only [h0, h466, hlam]
                · linarith only [h394, h466, hlam]
              · linarith only [h465, hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h394, h395, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p461_1]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h0, hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h4, hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h394, h395, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p461_1]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h395, hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h1, hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p461_1]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h1, h394, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p461_1]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h1, h394, h395, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p461_1]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h2, hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h394, hlam, p461_1]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h457, hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h459, hlam, p461_1]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h3, hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h394, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p461_1]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h458, hlam, p461_0]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [h1, h394, h458, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p461_1]
            · have p461_0 := h461c.1
              have p461_1 := h461c.2.1
              have p461_2 := h461c.2.2.1
              have p461_3 := h461c.2.2.2
              linarith only [hlam, p461_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h491 | h491
          · linarith only [h394, h395, h491, hlam]
          · rcases h1bigk with h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c | h493c
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h394, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p493_1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h457, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p493_1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              rcases p493_3 (m.d 0 1) (by simp) with h497 | h497
              · rcases p493_3 (m.d 1 2) (by simp) with h498 | h498
                · linarith only [h0, h498, hlam]
                · linarith only [h394, h498, hlam]
              · linarith only [h497, hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p493_1, u5ehi1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h0, hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h4, hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h4, h458, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p493_1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h395, hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h1, hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h458, hc12, hc35, hlam, hphi, ht23, p493_1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h394, h458, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p493_1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h458, hlam, p493_1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h2, hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h394, hlam, p493_1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h457, hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h491, hlam, p493_1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h3, hlam, p493_0]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h394, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p493_1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p493_1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [h3, h394, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p493_1]
            · have p493_0 := h493c.1
              have p493_1 := h493c.2.1
              have p493_2 := h493c.2.2.1
              have p493_3 := h493c.2.2.2
              linarith only [hlam, p493_0]
      · linarith only [h394, h4, h457, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h524 | h524
    · rcases m.htr 1 3 4 (by decide) (by decide) with h525 | h525
      · rcases m.htr 1 3 5 (by decide) (by decide) with h526 | h526
        · rcases m.htr 1 4 5 (by decide) (by decide) with h527 | h527
          · rcases h1bigk with h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h524, hc01, hlam, hphi, ht0b, ht5b, p528_1, u5ehi2]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h394, h524, h525, hc01, hlam, hphi, ht0b, ht5b, p528_1, u5ehi2]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h394, h524, hc01, hlam, hphi, ht0b, ht5b, p528_1, u5ehi2]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p528_1, u5ehi1]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h0, hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h4, hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h394, hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p528_1, u5ehi1]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h1, hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p528_1]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p528_1]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h1, h524, hc01, hlam, hphi, ht0b, ht5b, p528_1, u5ehi2]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h2, hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h524, hc14, hlam, hphi, ht01, ht0b, ht5b, p528_1, u5ehi2]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h525, hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h1, h524, h525, hc01, hlam, hphi, ht0b, ht5b, p528_1, u5ehi2]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h3, hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h524, hlam, p528_1]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h526, hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [h527, hlam, p528_0]
            · have p528_0 := h528c.1
              have p528_1 := h528c.2.1
              have p528_2 := h528c.2.2.1
              have p528_3 := h528c.2.2.2
              linarith only [hlam, p528_0]
          · linarith only [h394, h524, h527, hlam]
        · linarith only [h4, h524, h526, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h556 | h556
        · rcases m.htr 1 4 5 (by decide) (by decide) with h557 | h557
          · rcases h1bigk with h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h524, hc01, hlam, hphi, ht0b, ht5b, p558_1, u5ehi2]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h4, h524, hc01, hlam, hphi, ht0b, ht5b, p558_1, u5ehi2]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h557, hc01, hlam, hphi, ht0b, ht5b, p558_1, u5ehi4]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p558_1, u5ehi1]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h0, hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h4, hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h394, hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p558_1, u5ehi1]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h1, hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h525, hc12, hc34, hlam, hphi, ht23, p558_1]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h525, hlam, p558_1]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h524, h525, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p558_1, u5ehi2]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h2, hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h524, hc14, hlam, hphi, ht01, ht0b, ht5b, p558_1, u5ehi2]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p558_1]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h2, h524, hc01, hlam, hphi, ht0b, ht5b, p558_1, u5ehi2]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h3, hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h524, hlam, p558_1]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h556, hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [h557, hlam, p558_0]
            · have p558_0 := h558c.1
              have p558_1 := h558c.2.1
              have p558_2 := h558c.2.2.1
              have p558_3 := h558c.2.2.2
              linarith only [hlam, p558_0]
          · linarith only [h4, h524, h525, h557, hlam]
        · linarith only [h4, h524, h556, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h586 | h586
      · rcases m.htr 1 3 5 (by decide) (by decide) with h587 | h587
        · rcases m.htr 1 4 5 (by decide) (by decide) with h588 | h588
          · rcases h1bigk with h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              rcases p589_3 (m.d 0 1) (by simp) with h591 | h591
              · rcases p589_3 (m.d 1 2) (by simp) with h592 | h592
                · linarith only [h592, hlam, p589_0]
                · rcases p589_3 (m.d 1 3) (by simp) with h594 | h594
                  · linarith only [h1, h594, hlam]
                  · linarith only [h4, h594, hlam]
              · linarith only [h591, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h586, h588, hc01, hlam, hphi, ht0b, ht5b, p589_1, u5ehi4]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h588, hc01, hlam, hphi, ht0b, ht5b, p589_1, u5ehi4]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h587, hc01, hlam, hphi, ht0b, ht5b, p589_1, u5ehi3]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h0, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h4, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h394, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h524, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h1, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h1, h588, hc01, hlam, hphi, ht0b, ht5b, p589_1, u5ehi4]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h1, h587, hc01, hlam, hphi, ht0b, ht5b, p589_1, u5ehi3]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h2, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h586, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h1, h586, h587, hc01, hlam, hphi, ht0b, ht5b, p589_1, u5ehi3]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h3, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p589_1]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h587, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [h588, hlam, p589_0]
            · have p589_0 := h589c.1
              have p589_1 := h589c.2.1
              have p589_2 := h589c.2.2.1
              have p589_3 := h589c.2.2.2
              linarith only [hlam, p589_0]
          · rcases h1bigk with h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c | h621c
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              rcases p621_3 (m.d 0 1) (by simp) with h623 | h623
              · rcases p621_3 (m.d 1 2) (by simp) with h624 | h624
                · linarith only [h624, hlam, p621_0]
                · rcases p621_3 (m.d 1 3) (by simp) with h626 | h626
                  · linarith only [h1, h626, hlam]
                  · linarith only [h4, h626, hlam]
              · linarith only [h623, hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h587, hc01, hlam, hphi, ht0b, ht5b, p621_1, u5ehi1]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              rcases p621_3 (m.d 0 1) (by simp) with h631 | h631
              · rcases p621_3 (m.d 1 2) (by simp) with h632 | h632
                · linarith only [h0, h632, hlam]
                · rcases p621_3 (m.d 1 3) (by simp) with h634 | h634
                  · linarith only [h1, h634, hlam]
                  · linarith only [h586, h634, hlam]
              · linarith only [h631, hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h587, hc01, hlam, hphi, ht0b, ht5b, p621_1, u5ehi3]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h0, hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h4, hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h394, hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h524, hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h1, hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p621_1]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h1, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p621_1]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h1, h587, hc01, hlam, hphi, ht0b, ht5b, p621_1, u5ehi3]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h2, hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p621_1]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h586, hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h588, hlam, p621_1]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h3, hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p621_1]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h587, hlam, p621_0]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [h1, h587, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p621_1]
            · have p621_0 := h621c.1
              have p621_1 := h621c.2.1
              have p621_2 := h621c.2.2.1
              have p621_3 := h621c.2.2.2
              linarith only [hlam, p621_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h659 | h659
          · linarith only [h586, h587, h659, hlam]
          · rcases h1bigk with h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c | h661c
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              rcases p661_3 (m.d 0 1) (by simp) with h663 | h663
              · rcases p661_3 (m.d 1 2) (by simp) with h664 | h664
                · linarith only [h664, hlam, p661_0]
                · rcases p661_3 (m.d 1 3) (by simp) with h666 | h666
                  · linarith only [h1, h666, hlam]
                  · linarith only [h4, h666, hlam]
              · linarith only [h663, hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h586, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p661_1]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              rcases p661_3 (m.d 0 1) (by simp) with h671 | h671
              · rcases p661_3 (m.d 1 2) (by simp) with h672 | h672
                · linarith only [h0, h672, hlam]
                · rcases p661_3 (m.d 1 3) (by simp) with h674 | h674
                  · linarith only [h1, h674, hlam]
                  · linarith only [h586, h674, hlam]
              · linarith only [h671, hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h586, h587, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p661_1]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h0, hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h4, hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h394, hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h524, hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h1, hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p661_1]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h3, h587, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p661_1]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h587, hlam, p661_1]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h2, hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h659, hc12, hc45, hlam, hphi, ht23, ht34, p661_1]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h586, hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h659, hlam, p661_1]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h3, hlam, p661_0]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p661_1]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h3, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p661_1]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p661_1]
            · have p661_0 := h661c.1
              have p661_1 := h661c.2.1
              have p661_2 := h661c.2.2.1
              have p661_3 := h661c.2.2.2
              linarith only [hlam, p661_0]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h699 | h699
        · rcases m.htr 1 4 5 (by decide) (by decide) with h700 | h700
          · rcases h1bigk with h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c | h701c
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              rcases p701_3 (m.d 0 1) (by simp) with h703 | h703
              · rcases p701_3 (m.d 1 2) (by simp) with h704 | h704
                · linarith only [h704, hlam, p701_0]
                · rcases p701_3 (m.d 1 3) (by simp) with h706 | h706
                  · linarith only [h1, h706, hlam]
                  · linarith only [h4, h706, hlam]
              · linarith only [h703, hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h699, hc01, hlam, hphi, ht0b, ht5b, p701_1, u5ehi3]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h586, h699, hc01, hlam, hphi, ht0b, ht5b, p701_1, u5ehi3]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p701_1, u5ehi1]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h0, hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h4, hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h394, hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h524, hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h1, hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h586, hc12, hc34, hlam, hphi, ht23, p701_1]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h586, hlam, p701_1]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h586, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p701_1, u5ehi1]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h2, hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p701_1]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p701_1]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h2, h699, hc01, hlam, hphi, ht0b, ht5b, p701_1, u5ehi3]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h3, hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p701_1]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h699, hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [h700, hlam, p701_0]
            · have p701_0 := h701c.1
              have p701_1 := h701c.2.1
              have p701_2 := h701c.2.2.1
              have p701_3 := h701c.2.2.2
              linarith only [hlam, p701_0]
          · linarith only [h586, h699, h700, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h734 | h734
          · rcases h1bigk with h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c | h735c
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              rcases p735_3 (m.d 0 1) (by simp) with h737 | h737
              · rcases p735_3 (m.d 1 2) (by simp) with h738 | h738
                · linarith only [h738, hlam, p735_0]
                · rcases p735_3 (m.d 1 3) (by simp) with h740 | h740
                  · linarith only [h1, h740, hlam]
                  · linarith only [h4, h740, hlam]
              · linarith only [h737, hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              rcases p735_3 (m.d 0 1) (by simp) with h744 | h744
              · rcases p735_3 (m.d 1 2) (by simp) with h745 | h745
                · linarith only [h0, h745, hlam]
                · rcases p735_3 (m.d 1 3) (by simp) with h747 | h747
                  · linarith only [h747, hlam, p735_0]
                  · rcases p735_3 (m.d 1 4) (by simp) with h749 | h749
                    · linarith only [h2, h749, hlam]
                    · linarith only [h586, h749, hlam]
              · linarith only [h744, hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h734, hc01, hlam, hphi, ht0b, ht5b, p735_1, u5ehi4]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h734, hc01, hlam, hphi, ht0b, ht5b, p735_1, u5ehi4]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h0, hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h4, hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h394, hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h524, hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h1, hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h699, hc12, hc35, hlam, hphi, ht23, p735_1]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h586, hlam, p735_1]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h699, hlam, p735_1]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h2, hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h586, hc12, hc34, hlam, hphi, ht23, p735_1]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p735_1]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h2, h734, hc01, hlam, hphi, ht0b, ht5b, p735_1, u5ehi4]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h3, hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p735_1]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h3, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p735_1]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [h734, hlam, p735_0]
            · have p735_0 := h735c.1
              have p735_1 := h735c.2.1
              have p735_2 := h735c.2.2.1
              have p735_3 := h735c.2.2.2
              linarith only [hlam, p735_0]
          · rcases h1bigk with h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              rcases p775_3 (m.d 0 1) (by simp) with h777 | h777
              · rcases p775_3 (m.d 1 2) (by simp) with h778 | h778
                · linarith only [h778, hlam, p775_0]
                · rcases p775_3 (m.d 1 3) (by simp) with h780 | h780
                  · linarith only [h1, h780, hlam]
                  · linarith only [h4, h780, hlam]
              · linarith only [h777, hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              rcases p775_3 (m.d 0 1) (by simp) with h784 | h784
              · rcases p775_3 (m.d 1 2) (by simp) with h785 | h785
                · linarith only [h0, h785, hlam]
                · rcases p775_3 (m.d 1 3) (by simp) with h787 | h787
                  · linarith only [h787, hlam, p775_0]
                  · rcases p775_3 (m.d 1 4) (by simp) with h789 | h789
                    · linarith only [h2, h789, hlam]
                    · linarith only [h586, h789, hlam]
              · linarith only [h784, hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              rcases p775_3 (m.d 0 1) (by simp) with h793 | h793
              · rcases p775_3 (m.d 1 2) (by simp) with h794 | h794
                · linarith only [h0, h794, hlam]
                · rcases p775_3 (m.d 1 3) (by simp) with h796 | h796
                  · linarith only [h1, h796, hlam]
                  · rcases p775_3 (m.d 1 4) (by simp) with h798 | h798
                    · linarith only [h798, hlam, p775_0]
                    · rcases p775_3 (m.d 1 5) (by simp) with h800 | h800
                      · linarith only [h3, h800, hlam]
                      · linarith only [h734, h800, hlam]
              · linarith only [h793, hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [hc01, hlam, hphi, ht0b, ht5b, p775_1, u5ehi1]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h0, hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h4, hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h394, hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h524, hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h1, hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p775_1]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h586, hlam, p775_1]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h699, hlam, p775_1]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h2, hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p775_1]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p775_1]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h734, hlam, p775_1]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h3, hlam, p775_0]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p775_1]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h3, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p775_1]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p775_1]
            · have p775_0 := h775c.1
              have p775_1 := h775c.2.1
              have p775_2 := h775c.2.2.1
              have p775_3 := h775c.2.2.2
              linarith only [hlam, p775_0]

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_21_15_H_I_L_R_x0_x0_x0_x0_x0 m hb1 hb5 h0 h1 h2 h3 h4
  · exact r1l7_21_15_H_I_L_R_x0_x0_x0_x0_x1 m hb1 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h825 | h825
  · rcases m.htr 1 2 4 (by decide) (by decide) with h826 | h826
    · rcases m.htr 1 2 5 (by decide) (by decide) with h827 | h827
      · linarith only [h0, h3, h827, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h829 | h829
        · rcases m.htr 1 3 5 (by decide) (by decide) with h830 | h830
          · linarith only [h1, h3, h827, h830, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · linarith only [h0, h3, h825, h830, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h833 | h833
          · linarith only [h0, h3, h826, h829, h833, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · linarith only [h0, h3, h825, h833, hc23, hc35, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h836 | h836
      · linarith only [h2, h3, h826, h836, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h838 | h838
        · linarith only [h825, h826, h838, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h840 | h840
          · linarith only [h0, h3, h825, h836, h840, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · linarith only [h2, h3, h825, h826, h840, hc23, hc35, hlam, hphi]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h843 | h843
    · rcases m.htr 1 2 5 (by decide) (by decide) with h844 | h844
      · linarith only [h0, h3, h844, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h846 | h846
        · rcases m.htr 1 3 5 (by decide) (by decide) with h847 | h847
          · linarith only [h1, h3, h844, h847, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h849 | h849
            · linarith only [h1, h3, h825, h843, h847, h849, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · linarith only [h1, h3, h825, h843, h849, hc24, hc45, hlam, hphi]
        · linarith only [h825, h843, h846, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h853 | h853
      · linarith only [h1, h3, h825, h853, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h855 | h855
        · rcases m.htr 1 3 5 (by decide) (by decide) with h856 | h856
          · linarith only [h1, h3, h853, h856, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h858 | h858
            · linarith only [h1, h3, h855, h856, h858, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · linarith only [h1, h3, h855, h858, hc34, hc45, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h861 | h861
          · linarith only [h2, h3, h855, h861, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h863 | h863
            · linarith only [h2, h3, h861, h863, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases h1bigk with h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c | h865c
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h3, h863, hc12, hc45, hlam, hphi, ht23, ht34, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h3, h863, hc13, hc45, hlam, hphi, ht34, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h3, h863, hc14, hc45, hlam, hphi, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h3, hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h0, hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h825, hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h843, hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h853, hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h1, hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h855, hc12, hc34, hlam, hphi, ht23, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h855, hlam, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h861, hlam, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h2, hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h2, h3, h863, hc12, hc45, hlam, hphi, ht23, ht34, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h2, h3, h863, hc13, hc45, hlam, hphi, ht34, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hlam, p865_0]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h863, hlam, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h863, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h863, hc12, hc45, hlam, hphi, ht23, ht34, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h825, h863, hc12, hc45, hlam, hphi, ht23, ht34, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [h825, h855, h863, hc12, hc45, hlam, hphi, ht23, ht34, p865_1]
              · have p865_0 := h865c.1
                have p865_1 := h865c.2.1
                have p865_2 := h865c.2.2.1
                have p865_3 := h865c.2.2.2
                linarith only [hlam, p865_0]

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_21_15_H_I_L_R_x0_x0_x0_x0 m hb1 hb5 h0 h1 h2 h3
  · exact r1l7_21_15_H_I_L_R_x0_x0_x0_x1 m hb1 hb5 h0 h1 h2 h3

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h891 | h891
  · rcases m.htr 1 2 3 (by decide) (by decide) with h892 | h892
    · rcases m.htr 1 2 4 (by decide) (by decide) with h893 | h893
      · linarith only [h0, h2, h893, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h895 | h895
        · linarith only [h0, h2, h893, h895, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h897 | h897
          · linarith only [h1, h2, h897, hlam]
          · linarith only [h2, h891, h892, h895, h897, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h900 | h900
      · linarith only [h2, h891, h892, h900, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h902 | h902
        · linarith only [h1, h2, h892, h900, h902, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h904 | h904
          · linarith only [h1, h2, h904, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h906 | h906
            · linarith only [h1, h2, h904, h906, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h908 | h908
              · rcases h1bigk with h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h2, h904, hc12, hc34, hlam, hphi, ht23, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h2, h904, hc13, hc34, hlam, hphi, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h2, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h2, h904, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p909_1, u5ehi1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h0, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h892, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h900, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h902, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h1, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h906, hc12, hc35, hlam, hphi, ht23, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h904, hlam, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h906, hlam, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h904, hc01, hc34, hlam, hphi, ht12, ht23, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h904, hc12, hc34, hlam, hphi, ht23, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h904, hc13, hc34, hlam, hphi, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h904, h908, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p909_1, u5ehi4]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h891, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h891, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h2, h891, h892, h904, hc12, hc34, hlam, hphi, ht23, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h908, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [hlam, p909_0]
              · linarith only [h2, h891, h908, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h936 | h936
    · rcases m.htr 1 2 4 (by decide) (by decide) with h937 | h937
      · linarith only [h0, h2, h937, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h939 | h939
        · linarith only [h0, h2, h937, h939, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h941 | h941
          · linarith only [h1, h2, h941, hlam]
          · linarith only [h0, h2, h936, h941, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h944 | h944
      · linarith only [h1, h2, h936, h944, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h946 | h946
        · linarith only [h1, h2, h936, h944, h946, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h948 | h948
          · linarith only [h1, h2, h948, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h950 | h950
            · linarith only [h1, h2, h948, h950, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h952 | h952
              · rcases h1bigk with h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h891, h948, h952, hc12, hc34, hlam, hphi, ht23, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h891, h948, h952, hc13, hc34, hlam, hphi, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h2, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h891, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h0, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h936, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h944, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h946, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h1, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h1, h891, h948, h952, hc12, hc34, hlam, hphi, ht23, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h948, hlam, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h950, hlam, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h948, hc01, hc34, hlam, hphi, ht12, ht23, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h948, hc12, hc34, hlam, hphi, ht23, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h936, h948, hc12, hc34, hlam, hphi, ht23, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h948, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p953_1, u5ehi1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h1, h936, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h950, hc12, hc35, hlam, hphi, ht23, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h936, h950, hc12, hc35, hlam, hphi, ht23, p953_1]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [h952, hlam, p953_0]
                · have p953_0 := h953c.1
                  have p953_1 := h953c.2.1
                  have p953_2 := h953c.2.2.1
                  have p953_3 := h953c.2.2.2
                  linarith only [hlam, p953_0]
              · linarith only [h1, h2, h936, h952, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_21_15_H_I_L_R_x0_x0_x0 m hb1 hb5 h0 h1 h2
  · exact r1l7_21_15_H_I_L_R_x0_x0_x1 m hb1 hb5 h0 h1 h2

end R2N4
