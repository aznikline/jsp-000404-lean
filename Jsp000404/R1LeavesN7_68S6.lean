import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_68S4
import Jsp000404.R1LeavesN7_68S5

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_23_L_0_H_I_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h559 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h901 | h901
  · rcases m.htr 1 2 3 (by decide) (by decide) with h902 | h902
    · rcases m.htr 1 3 4 (by decide) (by decide) with h903 | h903
      · rcases m.htr 1 3 5 (by decide) (by decide) with h904 | h904
        · rcases m.htr 2 3 4 (by decide) (by decide) with h905 | h905
          · linarith only [h559, h901, h902, h905, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h907 | h907
            · rcases m.htr 3 4 5 (by decide) (by decide) with h908 | h908
              · rcases h3bigk with h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c | h909c
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h0, hlam, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p909_1, u0elo2]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h559, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h559, h908, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h0, h902, hc01, hc12, hlam, hphi, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h902, h907, h908, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h559, h901, h902, h908, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  rcases p909_3 (m.d 0 3) (by simp) with h919 | h919
                  · linarith only [h0, h919, hlam]
                  · linarith only [h901, h919, hlam]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h901, h908, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h902, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h905, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h905, h908, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h901, h908, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h903, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [hc23, hc34, hlam, hphi, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h902, h903, h908, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p909_1]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h901, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h904, hlam, p909_0]
                · have p909_0 := h909c.1
                  have p909_1 := h909c.2.1
                  have p909_2 := h909c.2.2.1
                  have p909_3 := h909c.2.2.2
                  linarith only [h907, hlam, p909_0]
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
              · linarith only [h559, h901, h908, hlam]
            · linarith only [h559, h901, h907, hc23, hc34, hlam, hphi]
        · linarith only [h559, h901, h903, h904, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h940 | h940
        · rcases m.htr 2 3 4 (by decide) (by decide) with h941 | h941
          · linarith only [h0, h903, h941, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h943 | h943
            · rcases m.htr 3 4 5 (by decide) (by decide) with h944 | h944
              · rcases h3bigk with h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c | h945c
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h0, hlam, p945_1]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p945_1, u0elo2]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h559, hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h559, hc35, hlam, hphi, ht0b, ht5b, p945_1, u0elo3]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h903, hc03, hc34, hlam, hphi, p945_1]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h903, hc23, hc34, hlam, hphi, p945_1]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h903, hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h903, h944, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h901, h944, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p945_1]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h902, hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h941, hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h902, h903, h944, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h901, h944, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p945_1]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [hc13, hc34, hlam, hphi, p945_1]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [hc23, hc34, hlam, hphi, p945_1]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  rcases p945_3 (m.d 0 3) (by simp) with h965 | h965
                  · linarith only [h559, h965, hlam]
                  · linarith only [h901, h965, hlam]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h901, hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h940, hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h943, hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [h944, hlam, p945_0]
                · have p945_0 := h945c.1
                  have p945_1 := h945c.2.1
                  have p945_2 := h945c.2.2.1
                  have p945_3 := h945c.2.2.2
                  linarith only [hlam, p945_0]
              · linarith only [h0, h903, h944, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h901, h903, h943, hc23, hc34, hlam, hphi]
        · linarith only [h0, h901, h940, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h976 | h976
      · rcases m.htr 1 3 5 (by decide) (by decide) with h977 | h977
        · rcases m.htr 2 3 4 (by decide) (by decide) with h978 | h978
          · rcases m.htr 2 3 5 (by decide) (by decide) with h979 | h979
            · rcases m.htr 3 4 5 (by decide) (by decide) with h980 | h980
              · rcases h3bigk with h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c | h981c
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [hlam, p981_0]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h0, hlam, p981_1]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h559, h902, h976, hlam, p981_1]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h559, hlam, p981_0]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h559, h902, h976, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p981_1]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h0, h902, hc01, hc23, hlam, hphi, ht12, p981_1]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [hlam, p981_0]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h902, hlam, p981_1]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h0, h559, h902, hc01, hc23, hlam, hphi, ht12, p981_1]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  rcases p981_3 (m.d 0 3) (by simp) with h991 | h991
                  · linarith only [h0, h991, hlam]
                  · linarith only [h901, h991, hlam]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h901, h980, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p981_1]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p981_1]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [hlam, p981_0]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h559, h901, h980, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p981_1]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  rcases p981_3 (m.d 0 3) (by simp) with h998 | h998
                  · linarith only [h559, h902, h976, h998, hlam]
                  · linarith only [h901, h998, hlam]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h976, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p981_1]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h976, hlam, p981_0]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h978, hlam, p981_0]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [hlam, p981_0]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h902, h976, h980, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p981_1]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h901, hlam, p981_0]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h977, hlam, p981_0]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h979, hlam, p981_0]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [h980, hlam, p981_0]
                · have p981_0 := h981c.1
                  have p981_1 := h981c.2.1
                  have p981_2 := h981c.2.2.1
                  have p981_3 := h981c.2.2.2
                  linarith only [hlam, p981_0]
              · linarith only [h559, h901, h980, hlam]
            · linarith only [h559, h901, h902, h979, hc13, hc34, hlam, hphi]
          · linarith only [h902, h976, h978, hlam]
        · linarith only [h559, h901, h976, h977, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1015 | h1015
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1016 | h1016
          · linarith only [h0, h1016, h976, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1018 | h1018
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1019 | h1019
              · rcases h3bigk with h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h0, hlam, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h0, h902, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1020_1, u0elo2]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h559, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1019, hc45, hlam, hphi, ht0b, ht5b, p1020_1, u0elo2]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1016, h902, hc03, hc34, hlam, hphi, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h902, hlam, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h976, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1016, h1019, h902, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1016, h1019, h901, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1016, hc13, hc34, hlam, hphi, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1016, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1016, h1019, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1019, h901, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [hc23, hc34, hlam, hphi, p1020_1]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  rcases p1020_3 (m.d 0 3) (by simp) with h1040 | h1040
                  · linarith only [h1040, h559, hlam]
                  · linarith only [h1040, h901, hlam]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h901, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1015, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1018, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [h1019, hlam, p1020_0]
                · have p1020_0 := h1020c.1
                  have p1020_1 := h1020c.2.1
                  have p1020_2 := h1020c.2.2.1
                  have p1020_3 := h1020c.2.2.2
                  linarith only [hlam, p1020_0]
              · linarith only [h0, h1019, h976, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h1018, h901, h902, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
        · linarith only [h0, h1015, h901, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1051 | h1051
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1052 | h1052
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1053 | h1053
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1054 | h1054
          · linarith only [h0, h1051, h1054, h559, hc01, hc12, hlam, hphi]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1056 | h1056
            · linarith only [h0, h1052, h1054, h1056, h901, hc01, hc13, hlam, hphi]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1058 | h1058
              · rcases h3bigk with h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c | h1059c
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h0, hlam, p1059_1]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1059_1, u0elo2]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h559, hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h901, hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h0, h1051, hc01, hc12, hlam, hphi, p1059_1]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  rcases p1059_3 (m.d 0 3) (by simp) with h1067 | h1067
                  · linarith only [h0, h1067, hlam]
                  · linarith only [h0, h1051, h1067, hc01, hc12, hlam, hphi, p1059_1]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h1051, h1058, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1059_1]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h0, h1051, h901, hc01, hc12, hlam, hphi, p1059_1]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1059_1]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h1051, hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h1054, hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h1056, hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1059_1]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h1052, hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h1051, h1052, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1059_1]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h0, h1051, h1052, h901, hc01, hc12, hlam, hphi, p1059_1]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1059_1]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h1053, hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h1051, h1053, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1059_1]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [h1058, hlam, p1059_0]
                · have p1059_0 := h1059c.1
                  have p1059_1 := h1059c.2.1
                  have p1059_2 := h1059c.2.2.1
                  have p1059_3 := h1059c.2.2.2
                  linarith only [hlam, p1059_0]
              · rcases h3bigk with h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h0, hlam, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1087_1, u0elo2]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h559, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h901, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h0, h1051, hc01, hc12, hlam, hphi, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  rcases p1087_3 (m.d 0 3) (by simp) with h1095 | h1095
                  · linarith only [h0, h1095, hlam]
                  · linarith only [h0, h1051, h1095, hc01, hc12, hlam, hphi, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h0, h1051, h559, hc01, hc12, hlam, hphi, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h0, h1051, h901, hc01, hc12, hlam, hphi, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1051, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1054, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1056, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1052, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1051, h1052, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1058, hlam, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h0, h1051, h1053, hc01, hc12, hlam, hphi, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1053, hlam, p1087_0]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1051, h1053, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [h1051, h1053, h559, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1087_1]
                · have p1087_0 := h1087c.1
                  have p1087_1 := h1087c.2.1
                  have p1087_2 := h1087c.2.2.1
                  have p1087_3 := h1087c.2.2.2
                  linarith only [hlam, p1087_0]
        · linarith only [h0, h1052, h1053, h559, hc01, hc35, hlam, hphi, ht12, ht23]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1116 | h1116
        · linarith only [h0, h1052, h1116, h901, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1118 | h1118
          · linarith only [h0, h1052, h1118, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1120 | h1120
            · linarith only [h1051, h1116, h1120, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1122 | h1122
              · rcases h3bigk with h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c | h1123c
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h0, hlam, p1123_1]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1123_1, u0elo2]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h559, hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h901, hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h1116, h1122, hc03, hc34, hlam, hphi, p1123_1]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h1116, h1122, hc23, hc34, hlam, hphi, p1123_1]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h1052, hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h1116, hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1123_1]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h1051, hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h1118, hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h1120, hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1123_1]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [hc13, hc34, hlam, hphi, p1123_1]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [hc23, hc34, hlam, hphi, p1123_1]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h0, h901, hc01, hc34, hlam, hphi, ht12, ht23, p1123_1]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1123_1]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1123_1]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [hc23, hc35, hlam, hphi, p1123_1]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [h1122, hlam, p1123_0]
                · have p1123_0 := h1123c.1
                  have p1123_1 := h1123c.2.1
                  have p1123_2 := h1123c.2.2.1
                  have p1123_3 := h1123c.2.2.2
                  linarith only [hlam, p1123_0]
              · linarith only [h0, h1052, h1122, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h1150 | h1150
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1151 | h1151
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1152 | h1152
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1153 | h1153
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1154 | h1154
              · rcases h3bigk with h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [hlam, p1155_0]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h0, hlam, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h1051, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1155_1, u0elo2]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h559, hlam, p1155_0]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h901, hlam, p1155_0]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h0, hc01, hc13, hlam, hphi, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [hlam, p1155_0]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h1051, hlam, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h1154, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h0, h1051, h901, hc01, hc23, hlam, hphi, ht12, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [hlam, p1155_0]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h0, h1154, h901, hc01, hc23, hlam, hphi, ht12, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h0, h901, hc01, hc23, hlam, hphi, ht12, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h0, h1150, hc01, hc13, hlam, hphi, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h1150, hlam, p1155_0]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h1152, hlam, p1155_0]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [hlam, p1155_0]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h0, h1051, h1150, h901, hc01, hc23, hlam, hphi, ht12, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h0, h1153, hc01, hc25, hlam, hphi, ht12, p1155_1]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h1151, hlam, p1155_0]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h1153, hlam, p1155_0]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [h1154, hlam, p1155_0]
                · have p1155_0 := h1155c.1
                  have p1155_1 := h1155c.2.1
                  have p1155_2 := h1155c.2.2.1
                  have p1155_3 := h1155c.2.2.2
                  linarith only [hlam, p1155_0]
              · rcases h3bigk with h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [hlam, p1181_0]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h0, hlam, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h1051, h1151, h901, hc05, hlam, hphi, ht0b, ht5b, p1181_1, u0elo2]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h559, hlam, p1181_0]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h901, hlam, p1181_0]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h0, h1051, hc01, hc23, hlam, hphi, ht12, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [hlam, p1181_0]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h1051, hlam, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h0, h1051, h559, hc01, hc23, hlam, hphi, ht12, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h0, h1051, h901, hc01, hc23, hlam, hphi, ht12, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [hlam, p1181_0]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h0, h559, hc01, hc23, hlam, hphi, ht12, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h0, h1154, h559, hc01, hc23, hlam, hphi, ht12, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h0, h1151, h1154, hc01, hc13, hlam, hphi, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h1150, hlam, p1181_0]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h1152, hlam, p1181_0]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [hlam, p1181_0]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h1154, hlam, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h0, h1151, hc01, hc13, hlam, hphi, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h1151, hlam, p1181_0]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h1153, hlam, p1181_0]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [h1151, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1181_1]
                · have p1181_0 := h1181c.1
                  have p1181_1 := h1181c.2.1
                  have p1181_2 := h1181c.2.2.1
                  have p1181_3 := h1181c.2.2.2
                  linarith only [hlam, p1181_0]
            · linarith only [h1051, h1151, h1153, hlam]
          · linarith only [h0, h1051, h1151, h1152, h901, hc01, hc34, hlam, hphi, ht12, ht23]
        · linarith only [h0, h1150, h1151, h559, hc01, hc35, hlam, hphi, ht12, ht23]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1210 | h1210
        · linarith only [h0, h1150, h1210, h901, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1212 | h1212
          · linarith only [h0, h1150, h1212, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1214 | h1214
            · linarith only [h0, h1210, h1214, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1216 | h1216
              · rcases h3bigk with h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, hlam, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1217_1, u0elo2]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h559, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h901, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, hc01, hc13, hlam, hphi, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h1051, hlam, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h1150, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h1210, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h1212, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h1214, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hc23, hc34, hlam, hphi, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, h901, hc01, hc34, hlam, hphi, ht12, ht23, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h0, h1051, hc01, hc35, hlam, hphi, ht12, ht23, p1217_1]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [h1216, hlam, p1217_0]
                · have p1217_0 := h1217c.1
                  have p1217_1 := h1217c.2.1
                  have p1217_2 := h1217c.2.2.1
                  have p1217_3 := h1217c.2.2.2
                  linarith only [hlam, p1217_0]
              · linarith only [h0, h1150, h1216, hc01, hc45, hlam, hphi, ht12, ht23, ht34]

theorem r1l7_10_23_L_0_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h559 | h559
  · exact r1l7_10_23_L_0_H_I_x1_x0 m hb0 hb3 h0 h559
  · exact r1l7_10_23_L_0_H_I_x1_x1 m hb0 hb3 h0 h559

theorem r1l7_10_23_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_23_L_0_H_I_x0 m hb0 hb3 h0
  · exact r1l7_10_23_L_0_H_I_x1 m hb0 hb3 h0

end R2N4
