import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9486000 in
set_option maxHeartbeats 9486000 in
theorem r1l7_21_14_M_LI_L_I_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2837 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3271 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3539 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3826 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h3827 | h3827
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3828 | h3828
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3829 | h3829
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3830 | h3830
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3831 | h3831
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3832 | h3832
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3833 | h3833
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3834 | h3834
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3835 | h3835
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3836 | h3836
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3837 | h3837
                      · linarith only [h3829, h3835, h3837, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h0, h3826, h3836, h3837, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3840 | h3840
                      · linarith only [h3835, h3836, h3840, hlam]
                      · rcases h1bigk with h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c | h3842c
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h0, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h2837, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3271, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3539, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hc01, hlam, hphi, p3842_1, u1elo1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h2837, hc01, hlam, hphi, p3842_1, u1elo1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p3842_1, u1elo1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p3842_1, u1elo1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hc01, hlam, hphi, p3842_1, u1elo2]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3829, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3271, h3828, h3829, h3835, h3836, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3842_1, u1elo1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3539, h3829, hc01, hlam, hphi, p3842_1, u1elo1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hc01, hlam, hphi, p3842_1, u1elo3]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3830, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3832, hlam, p3842_1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3539, h3829, h3832, hc01, hlam, hphi, p3842_1, u1elo1]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hc01, hlam, hphi, p3842_1, u1elo4]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3831, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3833, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [h3834, hlam, p3842_0]
                        · have p3842_0 := h3842c.1
                          have p3842_1 := h3842c.2.1
                          have p3842_2 := h3842c.2.2.1
                          have p3842_3 := h3842c.2.2.2
                          linarith only [hlam, p3842_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3868 | h3868
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3869 | h3869
                      · rcases h1bigk with h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c | h3870c
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h0, hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h2837, hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3271, hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3539, hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [hc01, hlam, hphi, p3870_1, u1elo1]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h2837, h3827, h3835, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3870_1, u1elo1]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p3870_1, u1elo1]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p3870_1, u1elo1]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [hc01, hlam, hphi, p3870_1, u1elo2]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3829, hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3539, h3829, h3834, hc01, hlam, hphi, p3870_1, u1elo1]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3539, h3829, hc01, hlam, hphi, p3870_1, u1elo1]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [hc01, hlam, hphi, p3870_1, u1elo3]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3830, hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3832, hlam, p3870_1]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3539, h3829, h3832, hc01, hlam, hphi, p3870_1, u1elo1]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [hc01, hlam, hphi, p3870_1, u1elo4]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3831, hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3833, hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [h3834, hlam, p3870_0]
                        · have p3870_0 := h3870c.1
                          have p3870_1 := h3870c.2.1
                          have p3870_2 := h3870c.2.2.1
                          have p3870_3 := h3870c.2.2.2
                          linarith only [hlam, p3870_0]
                      · linarith only [h0, h3826, h3835, h3868, h3869, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3897 | h3897
                      · linarith only [h2837, h3827, h3829, h3868, h3897, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h2837, h3827, h3828, h3829, h3835, h3897, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h2837, h3271, h3827, h3828, h3829, h3834, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3901 | h3901
                · linarith only [h3832, h3833, h3901, hlam]
                · linarith only [h2837, h3271, h3827, h3828, h3831, h3833, h3901, hc01, hlam, hphi, u1elo1]
            · linarith only [h2837, h3827, h3832, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3905 | h3905
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3906 | h3906
              · linarith only [h3829, h3831, h3906, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3908 | h3908
                · linarith only [h3830, h3831, h3908, hlam]
                · linarith only [h3271, h3828, h3908, hlam]
            · linarith only [h2837, h3827, h3905, hlam]
        · linarith only [h0, h3826, h3830, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3913 | h3913
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3914 | h3914
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3915 | h3915
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3916 | h3916
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3917 | h3917
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3918 | h3918
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3919 | h3919
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3920 | h3920
                      · rcases h1bigk with h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h0, hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h2837, hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3271, hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3539, hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [hc01, hlam, hphi, p3921_1, u1elo1]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3829, hlam, p3921_1]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3271, h3829, hc01, hlam, hphi, p3921_1, u1elo2]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3539, h3829, hc01, hlam, hphi, p3921_1, u1elo2]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [hc01, hlam, hphi, p3921_1, u1elo2]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, p3921_1, u1elo2]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p3921_1, u1elo2]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p3921_1, u1elo2]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [hc01, hlam, hphi, p3921_1, u1elo3]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3913, hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3915, hlam, p3921_1]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3539, h3913, hc01, hlam, hphi, p3921_1, u1elo1]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [hc01, hlam, hphi, p3921_1, u1elo4]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3914, hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3916, hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [h3917, hlam, p3921_0]
                        · have p3921_0 := h3921c.1
                          have p3921_1 := h3921c.2.1
                          have p3921_2 := h3921c.2.2.1
                          have p3921_3 := h3921c.2.2.2
                          linarith only [hlam, p3921_0]
                      · linarith only [h0, h3826, h3829, h3919, h3920, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3948 | h3948
                      · linarith only [h3918, h3919, h3948, hlam]
                      · rcases h1bigk with h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c | h3950c
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h0, hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h2837, hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3271, hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3539, hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3829, hc01, hc23, hlam, hphi, ht12, p3950_1]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3829, hlam, p3950_1]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3271, h3829, hc01, hc23, hlam, hphi, ht12, p3950_1]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3539, h3829, hc01, hc23, hlam, hphi, ht12, p3950_1]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [hc01, hlam, hphi, p3950_1, u1elo2]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, p3950_1, u1elo2]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3271, h3828, h3918, h3919, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3950_1, u1elo2]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p3950_1, u1elo2]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [hc01, hlam, hphi, p3950_1, u1elo3]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3913, hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3915, hlam, p3950_1]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3539, h3829, h3913, hc01, hc23, hlam, hphi, ht12, p3950_1]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [hc01, hlam, hphi, p3950_1, u1elo4]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3914, hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3916, hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [h3917, hlam, p3950_0]
                        · have p3950_0 := h3950c.1
                          have p3950_1 := h3950c.2.1
                          have p3950_2 := h3950c.2.2.1
                          have p3950_3 := h3950c.2.2.2
                          linarith only [hlam, p3950_0]
                  · linarith only [h0, h3829, h3918, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h3271, h3826, h3828, h3917, hc01, hlam, hphi, u1elo1]
              · linarith only [h3829, h3914, h3916, hlam]
            · linarith only [h2837, h3827, h3915, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3980 | h3980
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3981 | h3981
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3982 | h3982
                · linarith only [h3913, h3914, h3982, hlam]
                · linarith only [h3271, h3539, h3828, h3981, h3982, hc01, hlam, hphi, u1elo2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3985 | h3985
                · linarith only [h3913, h3914, h3985, hlam]
                · linarith only [h0, h3271, h3826, h3828, h3985, hc01, hlam, hphi, u1elo1]
            · linarith only [h2837, h3827, h3980, hlam]
        · linarith only [h0, h3826, h3913, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3990 | h3990
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3991 | h3991
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3992 | h3992
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3993 | h3993
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3994 | h3994
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3995 | h3995
                · linarith only [h3271, h3828, h3995, hc01, hlam, hphi, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3997 | h3997
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3998 | h3998
                    · linarith only [h3271, h3995, h3998, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4000 | h4000
                      · linarith only [h3271, h3995, h4000, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases h1bigk with h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c | h4002c
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h0, hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h2837, hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3271, hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3539, hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [hc01, hlam, hphi, p4002_1, u1elo1]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3994, hc35, hlam, hphi, ht01, ht0b, ht5b, p4002_1, u1elo1]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4002_1, u1elo1]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3271, h3995, hc01, hlam, hphi, p4002_1, u1elo1]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [hc01, hlam, hphi, p4002_1, u1elo2]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3990, hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3271, h3990, hc01, hlam, hphi, p4002_1, u1elo1]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3271, h3990, h3995, hc01, hlam, hphi, p4002_1, u1elo1]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [hc01, hlam, hphi, p4002_1, u1elo3]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3991, hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3993, hlam, p4002_1]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3995, hlam, p4002_1]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [hc01, hlam, hphi, p4002_1, u1elo4]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3992, hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3994, hlam, p4002_0]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [h3271, h3990, h3994, hc01, hlam, hphi, p4002_1, u1elo1]
                        · have p4002_0 := h4002c.1
                          have p4002_1 := h4002c.2.1
                          have p4002_2 := h4002c.2.2.1
                          have p4002_3 := h4002c.2.2.2
                          linarith only [hlam, p4002_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4028 | h4028
                    · linarith only [h3827, h3828, h3997, h4028, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4030 | h4030
                      · linarith only [h2837, h3271, h3827, h3990, h3995, h4030, hc01, hlam, hphi, u1elo1]
                      · rcases h1bigk with h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c | h4032c
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h0, hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h2837, hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3271, hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3539, hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [hc01, hlam, hphi, p4032_1, u1elo1]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h2837, h3827, h3997, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4032_1, u1elo1]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4032_1, u1elo1]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p4032_1, u1elo1]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [hc01, hlam, hphi, p4032_1, u1elo2]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3990, hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3271, h3990, hc01, hlam, hphi, p4032_1, u1elo1]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3539, h3990, hc01, hlam, hphi, p4032_1, u1elo1]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [hc01, hlam, hphi, p4032_1, u1elo3]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3991, hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3993, hlam, p4032_1]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3995, hlam, p4032_1]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [hc01, hlam, hphi, p4032_1, u1elo4]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3992, hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3994, hlam, p4032_0]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [h3271, h3990, h3994, hc01, hlam, hphi, p4032_1, u1elo1]
                        · have p4032_0 := h4032c.1
                          have p4032_1 := h4032c.2.1
                          have p4032_2 := h4032c.2.2.1
                          have p4032_3 := h4032c.2.2.2
                          linarith only [hlam, p4032_0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4058 | h4058
                · linarith only [h3271, h3828, h4058, hc01, hlam, hphi, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4060 | h4060
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4061 | h4061
                    · linarith only [h3271, h4058, h4061, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4063 | h4063
                      · linarith only [h3271, h4058, h4060, h4063, hc01, hc24, hlam, hphi, ht12]
                      · rcases h1bigk with h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c | h4065c
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [hlam, p4065_0]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h0, hlam, p4065_0]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h2837, hlam, p4065_0]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3271, hlam, p4065_0]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3539, hlam, p4065_0]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [hc01, hlam, hphi, p4065_1, u1elo1]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [hlam, p4065_0]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h2837, hc01, hlam, hphi, p4065_1, u1elo1]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4065_1, u1elo1]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3271, h3993, h3994, hc01, hlam, hphi, p4065_1, u1elo1]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [hc01, hlam, hphi, p4065_1, u1elo2]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3990, hlam, p4065_0]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [hlam, p4065_0]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3271, h3992, h3994, hc01, hlam, hphi, p4065_1, u1elo1]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3994, hlam, p4065_1]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [hc01, hlam, hphi, p4065_1, u1elo3]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3991, hlam, p4065_0]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3993, hlam, p4065_1]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [hlam, p4065_0]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h4058, hlam, p4065_1]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3992, hc01, hlam, hphi, p4065_1, u1elo1]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3992, hlam, p4065_0]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h2837, h3992, hc01, hlam, hphi, p4065_1, u1elo1]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [h3271, h3992, hc01, hlam, hphi, p4065_1, u1elo1]
                        · have p4065_0 := h4065c.1
                          have p4065_1 := h4065c.2.1
                          have p4065_2 := h4065c.2.2.1
                          have p4065_3 := h4065c.2.2.2
                          linarith only [hlam, p4065_0]
                  · linarith only [h2837, h3827, h3994, h4060, hc23, hc35, hlam, hphi]
            · linarith only [h2837, h3827, h3993, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4093 | h4093
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4094 | h4094
              · linarith only [h3990, h3992, h4094, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4096 | h4096
                · linarith only [h3271, h3828, h4096, hc01, hlam, hphi, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4098 | h4098
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4099 | h4099
                    · linarith only [h3271, h4096, h4099, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h3990, h3992, h4098, h4099, hc34, hc45, hlam, hphi]
                  · linarith only [h2837, h3827, h4094, h4098, hc23, hc35, hlam, hphi]
            · linarith only [h2837, h3827, h4093, hlam]
        · linarith only [h0, h3826, h3991, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4105 | h4105
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4106 | h4106
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4107 | h4107
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4108 | h4108
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4109 | h4109
                · linarith only [h3271, h3828, h4105, h4109, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4111 | h4111
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4112 | h4112
                    · linarith only [h3271, h4109, h4112, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4114 | h4114
                      · linarith only [h0, h3271, h3826, h3990, h4109, h4111, h4114, hc01, hlam, hphi, u1elo2]
                      · rcases h1bigk with h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c | h4116c
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [hlam, p4116_0]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h0, hlam, p4116_0]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h2837, hlam, p4116_0]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h3271, hlam, p4116_0]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h3539, hlam, p4116_0]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h3990, hc01, hlam, hphi, p4116_1, u1elo2]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [hlam, p4116_0]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h3990, hlam, p4116_1]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h3271, h3990, hc01, hlam, hphi, p4116_1, u1elo2]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h3539, h3990, hc01, hlam, hphi, p4116_1, u1elo2]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [hc01, hlam, hphi, p4116_1, u1elo2]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h0, h3826, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4116_1, u1elo2]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [hlam, p4116_0]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4116_1, u1elo2]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h3271, h3539, h3828, hc01, hlam, hphi, p4116_1, u1elo2]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h4105, hc01, hlam, hphi, p4116_1, u1elo1]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h4105, hlam, p4116_0]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h4107, hlam, p4116_1]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [hlam, p4116_0]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h4109, hlam, p4116_1]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [hc01, hlam, hphi, p4116_1, u1elo4]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h4106, hlam, p4116_0]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h4108, hlam, p4116_0]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [h3271, h3990, h4106, hc01, hc23, hlam, hphi, ht12, p4116_1]
                        · have p4116_0 := h4116c.1
                          have p4116_1 := h4116c.2.1
                          have p4116_2 := h4116c.2.2.1
                          have p4116_3 := h4116c.2.2.2
                          linarith only [hlam, p4116_0]
                  · linarith only [h0, h3990, h4111, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h3990, h4106, h4108, hlam]
            · linarith only [h0, h3271, h3827, h3990, h4107, hc01, hlam, hphi, u1elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4145 | h4145
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4146 | h4146
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4147 | h4147
                · linarith only [h3271, h3828, h4105, h4147, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4149 | h4149
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4150 | h4150
                    · linarith only [h3271, h4147, h4150, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4152 | h4152
                      · linarith only [h0, h3826, h4106, h4149, h4150, h4152, hlam]
                      · rcases h1bigk with h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c | h4154c
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [hlam, p4154_0]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h0, hlam, p4154_0]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h2837, hlam, p4154_0]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h3271, hlam, p4154_0]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h3539, hlam, p4154_0]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h4106, h4150, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4154_1]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [hlam, p4154_0]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h3990, hlam, p4154_1]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h3271, h4106, h4150, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4154_1]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h4106, hlam, p4154_1]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [hc01, hlam, hphi, p4154_1, u1elo2]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h0, h3826, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4154_1, u1elo2]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [hlam, p4154_0]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4154_1, u1elo2]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p4154_1, u1elo2]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [hc01, hlam, hphi, p4154_1, u1elo3]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h4105, hlam, p4154_0]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h4145, hlam, p4154_1]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [hlam, p4154_0]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h4147, hlam, p4154_1]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [hc01, hlam, hphi, p4154_1, u1elo4]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, p4154_1, u1elo4]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h4146, hlam, p4154_0]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [h3271, h4146, hc01, hlam, hphi, p4154_1, u1elo2]
                        · have p4154_0 := h4154c.1
                          have p4154_1 := h4154c.2.1
                          have p4154_2 := h4154c.2.2.1
                          have p4154_3 := h4154c.2.2.2
                          linarith only [hlam, p4154_0]
                  · linarith only [h3271, h3990, h4105, h4149, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4181 | h4181
                · linarith only [h3271, h3828, h4105, h4181, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4183 | h4183
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4184 | h4184
                    · linarith only [h3271, h4181, h4184, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4186 | h4186
                      · linarith only [h0, h3826, h4106, h4183, h4184, h4186, hlam]
                      · rcases h1bigk with h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [hlam, p4188_0]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h0, hlam, p4188_0]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h2837, hlam, p4188_0]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h3271, hlam, p4188_0]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h3539, hlam, p4188_0]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h3990, h4146, h4186, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4188_1]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [hlam, p4188_0]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h3990, hlam, p4188_1]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h3990, h4146, h4186, hc14, hc45, hlam, hphi, p4188_1]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h4106, hlam, p4188_1]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h4146, h4186, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4188_1]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h0, h4146, h4186, hc02, hc45, hlam, hphi, ht23, ht34, p4188_1]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [hlam, p4188_0]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h3271, h4146, h4186, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4188_1]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h4146, hlam, p4188_1]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h4105, hc01, hlam, hphi, p4188_1, u1elo1]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h4105, hlam, p4188_0]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h4145, hlam, p4188_1]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [hlam, p4188_0]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h4181, hlam, p4188_1]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [hc01, hlam, hphi, p4188_1, u1elo4]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, p4188_1, u1elo4]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h2837, hc01, hlam, hphi, p4188_1, u1elo4]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4188_1, u1elo4]
                        · have p4188_0 := h4188c.1
                          have p4188_1 := h4188c.2.1
                          have p4188_2 := h4188c.2.2.1
                          have p4188_3 := h4188c.2.2.2
                          linarith only [hlam, p4188_0]
                  · linarith only [h3271, h3827, h3990, h4105, h4183, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
            · linarith only [h2837, h3827, h4145, hlam]
        · linarith only [h0, h3826, h4105, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4217 | h4217
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4218 | h4218
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4219 | h4219
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4220 | h4220
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4221 | h4221
            · linarith only [h2837, h3827, h4218, h4221, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4223 | h4223
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4224 | h4224
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4225 | h4225
                  · linarith only [h3539, h4218, h4221, h4223, h4225, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4227 | h4227
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4228 | h4228
                      · rcases h1bigk with h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c | h4229c
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h0, hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h2837, hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h3271, hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h3539, hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [hc01, hlam, hphi, p4229_1, u1elo1]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h3539, h4223, hc01, hlam, hphi, p4229_1, u1elo1]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4229_1, u1elo1]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p4229_1, u1elo1]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [hc01, hlam, hphi, p4229_1, u1elo2]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h4218, hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h4221, hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p4229_1, u1elo2]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [hc01, hlam, hphi, p4229_1, u1elo3]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h4219, hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h2837, hc01, hlam, hphi, p4229_1, u1elo3]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h3539, h4219, hc01, hlam, hphi, p4229_1, u1elo1]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h4223, hc01, hlam, hphi, p4229_1, u1elo2]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h4220, hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h4223, hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [h4224, hlam, p4229_0]
                        · have p4229_0 := h4229c.1
                          have p4229_1 := h4229c.2.1
                          have p4229_2 := h4229c.2.2.1
                          have p4229_3 := h4229c.2.2.2
                          linarith only [hlam, p4229_0]
                      · linarith only [h0, h3826, h4221, h4227, h4228, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4256 | h4256
                      · linarith only [h4221, h4223, h4225, h4227, h4256, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h3826, h4217, h4221, h4256, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h3271, h3826, h4217, h4224, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4260 | h4260
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4261 | h4261
                  · linarith only [h2837, h4221, h4261, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4263 | h4263
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4264 | h4264
                      · rcases h1bigk with h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c | h4265c
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h0, hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h2837, hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h3271, hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h3539, hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [hc01, hlam, hphi, p4265_1, u1elo1]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h2837, hc01, hlam, hphi, p4265_1, u1elo1]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4265_1, u1elo1]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h2837, h4223, hc01, hlam, hphi, p4265_1, u1elo1]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [hc01, hlam, hphi, p4265_1, u1elo2]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h4218, hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h4221, hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h4223, hlam, p4265_1]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [hc01, hlam, hphi, p4265_1, u1elo3]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h4219, hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h2837, h4219, hc01, hlam, hphi, p4265_1, u1elo1]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h3539, h4219, hc01, hlam, hphi, p4265_1, u1elo1]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [hc01, hlam, hphi, p4265_1, u1elo4]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h4220, hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h2837, h4220, hc01, hlam, hphi, p4265_1, u1elo1]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [h4260, hlam, p4265_0]
                        · have p4265_0 := h4265c.1
                          have p4265_1 := h4265c.2.1
                          have p4265_2 := h4265c.2.2.1
                          have p4265_3 := h4265c.2.2.2
                          linarith only [hlam, p4265_0]
                      · linarith only [h0, h3826, h4263, h4264, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4292 | h4292
                      · rcases h1bigk with h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h0, hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h2837, hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h3271, hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h3539, hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [hc01, hlam, hphi, p4293_1, u1elo1]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h2837, hc01, hlam, hphi, p4293_1, u1elo1]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h3271, hc01, hlam, hphi, p4293_1, u1elo1]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h3539, hc01, hlam, hphi, p4293_1, u1elo1]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [hc01, hlam, hphi, p4293_1, u1elo2]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h4218, hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h4221, hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h4223, hlam, p4293_1]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [hc01, hlam, hphi, p4293_1, u1elo3]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h4219, hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h2837, h4219, hc01, hlam, hphi, p4293_1, u1elo1]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h2837, h4219, h4223, hc01, hlam, hphi, p4293_1, u1elo1]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [hc01, hlam, hphi, p4293_1, u1elo4]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h4220, hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h2837, h4220, hc01, hlam, hphi, p4293_1, u1elo1]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [h4260, hlam, p4293_0]
                        · have p4293_0 := h4293c.1
                          have p4293_1 := h4293c.2.1
                          have p4293_2 := h4293c.2.2.1
                          have p4293_3 := h4293c.2.2.2
                          linarith only [hlam, p4293_0]
                      · linarith only [h0, h2837, h3826, h3827, h4217, h4292, hc01, hlam, hphi, u1elo1]
                · linarith only [h0, h3271, h3826, h4217, h4260, hc01, hlam, hphi, u1elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4321 | h4321
            · linarith only [h2837, h3827, h4321, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4323 | h4323
              · linarith only [h4219, h4220, h4321, h4323, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4325 | h4325
                · linarith only [h4219, h4220, h4325, hlam]
                · linarith only [h0, h2837, h3826, h4217, h4220, h4321, h4325, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h3826, h4219, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4329 | h4329
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4330 | h4330
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4331 | h4331
            · linarith only [h2837, h3827, h4331, hc01, hlam, hphi, u1elo2]
            · linarith only [h4218, h4329, h4331, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4334 | h4334
            · linarith only [h2837, h3827, h4334, hc01, hlam, hphi, u1elo2]
            · linarith only [h4218, h4329, h4334, hlam]
        · linarith only [h0, h3826, h4329, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4338 | h4338
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4339 | h4339
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4340 | h4340
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4341 | h4341
            · linarith only [h2837, h3827, h4338, h4341, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4343 | h4343
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4344 | h4344
                · linarith only [h2837, h3827, h4217, h4339, h4344, hc01, hlam, hphi, u1elo1]
                · linarith only [h4341, h4343, h4344, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4347 | h4347
                · linarith only [h2837, h3827, h4217, h4347, hc01, hlam, hphi, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4349 | h4349
                  · linarith only [h2837, h3827, h4338, h4349, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4351 | h4351
                    · linarith only [h2837, h4341, h4347, h4351, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4353 | h4353
                      · linarith only [h2837, h4341, h4347, h4353, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h2837, h4341, h4353, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4356 | h4356
            · linarith only [h2837, h3827, h4356, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4358 | h4358
              · linarith only [h4339, h4340, h4356, h4358, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4360 | h4360
                · linarith only [h2837, h3827, h4217, h4339, h4340, h4360, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4362 | h4362
                  · linarith only [h2837, h4356, h4362, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4364 | h4364
                    · linarith only [h3271, h4360, h4364, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4366 | h4366
                      · linarith only [h0, h3826, h4340, h4362, h4364, h4366, hc23, hc34, hlam, hphi]
                      · linarith only [h2837, h4356, h4366, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h3826, h4339, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4370 | h4370
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4371 | h4371
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4372 | h4372
            · linarith only [h2837, h3827, h4372, hc01, hlam, hphi, u1elo2]
            · linarith only [h4338, h4370, h4372, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4375 | h4375
            · linarith only [h2837, h3827, h4375, hc01, hlam, hphi, u1elo2]
            · linarith only [h4338, h4370, h4375, hlam]
        · linarith only [h0, h3826, h4370, hlam]

end R2N4
