import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_63S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3012000 in
set_option maxHeartbeats 3012000 in
theorem r1l7_11_25_L_0_M_LI_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h820 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h916 | h916
  · rcases m.htr 0 4 5 (by decide) (by decide) with h917 | h917
    · rcases m.htr 1 2 4 (by decide) (by decide) with h918 | h918
      · rcases m.htr 1 2 5 (by decide) (by decide) with h919 | h919
        · rcases m.htr 1 3 5 (by decide) (by decide) with h920 | h920
          · rcases m.htr 1 4 5 (by decide) (by decide) with h921 | h921
            · rcases m.htr 2 3 4 (by decide) (by decide) with h922 | h922
              · rcases m.htr 2 3 5 (by decide) (by decide) with h923 | h923
                · rcases m.htr 2 4 5 (by decide) (by decide) with h924 | h924
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h925 | h925
                    · rcases h5bigk with h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h919, h923, h925, hc45, hlam, hphi, p926_1, u5elo0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h820, h916, h918, h923, h925, hc45, hlam, hphi, ht01, ht0b, ht5b, p926_1, u1elo1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h820, h916, h918, h925, hc45, hlam, hphi, ht01, ht0b, ht5b, p926_1, u1elo1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h820, h916, h918, hc45, hlam, hphi, ht01, ht0b, ht5b, p926_1, u1elo1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h916, hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h820, h916, h918, h923, h925, hc45, hlam, hphi, ht01, ht0b, ht5b, p926_1, u1elo1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h820, h916, h918, h925, hc45, hlam, hphi, ht01, ht0b, ht5b, p926_1, u1elo1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h820, h916, h918, hc45, hlam, hphi, ht01, ht0b, ht5b, p926_1, u1elo1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hc05, hlam, hphi, p926_1, u5elo2]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h919, hlam, p926_1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h820, h916, h918, h919, h925, hc45, hlam, hphi, ht01, ht0b, ht5b, p926_1, u1elo1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h820, h916, h918, h919, hc45, hlam, hphi, ht01, ht0b, ht5b, p926_1, u1elo1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hc05, hlam, hphi, p926_1, u5elo3]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h920, hlam, p926_1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h923, hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hlam, p926_0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h916, h919, h923, hc45, hlam, hphi, p926_1, u5elo0]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h917, hlam, p926_1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h921, hlam, p926_1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h924, hlam, p926_1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [h925, hlam, p926_1]
                      · have p926_0 := h926c.1
                        have p926_1 := h926c.2.1
                        have p926_2 := h926c.2.2.1
                        have p926_3 := h926c.2.2.2
                        linarith only [hlam, p926_0]
                    · linarith only [h820, h916, h918, h921, h925, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h820, h916, h918, h921, h924, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · linarith only [h922, h923, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h955 | h955
                · rcases m.htr 2 4 5 (by decide) (by decide) with h956 | h956
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h957 | h957
                    · rcases h5bigk with h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c | h958c
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [hlam, p958_0]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [hc15, hlam, hphi, p958_1, u5elo0]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h820, h916, h918, h955, h957, hc45, hlam, hphi, ht01, ht0b, ht5b, p958_1, u1elo1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h820, h916, h918, h957, hc45, hlam, hphi, ht01, ht0b, ht5b, p958_1, u1elo1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h820, h916, h918, hc45, hlam, hphi, ht01, ht0b, ht5b, p958_1, u1elo1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h916, hlam, p958_0]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [hlam, p958_0]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h820, h916, h918, h955, h957, hc45, hlam, hphi, ht01, ht0b, ht5b, p958_1, u1elo1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h820, h916, h918, h957, hc45, hlam, hphi, ht01, ht0b, ht5b, p958_1, u1elo1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h820, h916, h918, hc45, hlam, hphi, ht01, ht0b, ht5b, p958_1, u1elo1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [hc05, hlam, hphi, p958_1, u5elo2]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h919, hlam, p958_1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [hlam, p958_0]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h957, hc45, hlam, hphi, p958_1, u5elo2]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h820, h916, h918, h919, hc45, hlam, hphi, ht01, ht0b, ht5b, p958_1, u1elo1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h922, h955, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p958_1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h920, hlam, p958_1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h955, hlam, p958_0]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [hlam, p958_0]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h916, h919, h955, hc45, hlam, hphi, p958_1, u5elo0]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h917, hlam, p958_1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h921, hlam, p958_1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h956, hlam, p958_1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [h957, hlam, p958_1]
                      · have p958_0 := h958c.1
                        have p958_1 := h958c.2.1
                        have p958_2 := h958c.2.2.1
                        have p958_3 := h958c.2.2.2
                        linarith only [hlam, p958_0]
                    · linarith only [h820, h916, h918, h921, h957, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h820, h916, h918, h921, h922, h956, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h820, h916, h918, h920, h955, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
            · linarith only [h820, h921, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h988 | h988
            · rcases m.htr 2 3 4 (by decide) (by decide) with h989 | h989
              · rcases m.htr 2 3 5 (by decide) (by decide) with h990 | h990
                · linarith only [h820, h916, h918, h919, h920, h990, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h989, h990, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h993 | h993
                · linarith only [h920, h989, h993, hc13, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h995 | h995
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h996 | h996
                    · rcases h5bigk with h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [hlam, p997_0]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h820, h916, h918, hc15, hlam, hphi, ht01, ht0b, ht5b, p997_1, u1elo1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h820, h916, h918, h993, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p997_1, u1elo1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h820, h916, h918, h920, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p997_1, u1elo1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h820, h916, h918, hc45, hlam, hphi, ht01, ht0b, ht5b, p997_1, u1elo1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h916, hlam, p997_0]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [hlam, p997_0]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h993, hc23, hlam, hphi, ht34, ht45, p997_1, u5elo1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h920, hlam, p997_0]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h820, h916, h918, hc45, hlam, hphi, ht01, ht0b, ht5b, p997_1, u1elo1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [hc05, hlam, hphi, p997_1, u5elo2]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h919, hlam, p997_1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [hlam, p997_0]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h993, hlam, p997_1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h820, h916, h918, h919, hc45, hlam, hphi, ht01, ht0b, ht5b, p997_1, u1elo1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [hc05, hlam, hphi, p997_1, u5elo3]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h919, hc25, hlam, hphi, p997_1, u5elo3]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [hc25, hlam, hphi, p997_1, u5elo3]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [hlam, p997_0]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [hc45, hlam, hphi, p997_1, u5elo3]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h917, hlam, p997_1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h988, hlam, p997_1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h995, hlam, p997_1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [h996, hlam, p997_1]
                      · have p997_0 := h997c.1
                        have p997_1 := h997c.2.1
                        have p997_2 := h997c.2.2.1
                        have p997_3 := h997c.2.2.2
                        linarith only [hlam, p997_0]
                    · linarith only [h820, h916, h918, h988, h996, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h820, h916, h918, h988, h995, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · linarith only [h820, h988, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
        · linarith only [h820, h918, h919, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1027 | h1027
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1028 | h1028
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1029 | h1029
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1030 | h1030
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1031 | h1031
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1032 | h1032
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1033 | h1033
                    · rcases h5bigk with h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [hlam, p1034_0]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h1027, h1031, h1033, hc45, hlam, hphi, p1034_1, u5elo0]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h0, h1031, h1033, h916, hc45, hlam, hphi, ht01, ht0b, ht5b, p1034_1, u1elo1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h0, h1030, h1033, h916, h918, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h0, h1030, h916, h918, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h916, hlam, p1034_0]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [hlam, p1034_0]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h1031, h1033, hc45, hlam, hphi, p1034_1, u5elo1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h0, h1030, h1033, h916, h918, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h0, h1030, h916, h918, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [hc05, hlam, hphi, p1034_1, u5elo2]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h1027, hlam, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [hlam, p1034_0]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h1033, hc45, hlam, hphi, p1034_1, u5elo2]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h0, h1027, h1030, h916, h918, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [hc05, hlam, hphi, p1034_1, u5elo3]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h1028, hlam, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h1031, hlam, p1034_0]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [hlam, p1034_0]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h0, h1027, h1030, h1031, h916, h918, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h917, hlam, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h1029, hlam, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h1032, hlam, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [h1033, hlam, p1034_1]
                      · have p1034_0 := h1034c.1
                        have p1034_1 := h1034c.2.1
                        have p1034_2 := h1034c.2.2.1
                        have p1034_3 := h1034c.2.2.2
                        linarith only [hlam, p1034_0]
                    · linarith only [h0, h1029, h1030, h1033, h916, h918, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1029, h1032, h916, h918, hlam]
                · linarith only [h0, h1030, h1031, h918, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1063 | h1063
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1064 | h1064
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1065 | h1065
                    · rcases h5bigk with h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c | h1066c
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [hlam, p1066_0]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h0, h1027, h1063, h1065, h916, hc45, hlam, hphi, ht01, ht0b, ht5b, p1066_1, u1elo1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h0, h1030, h1063, h1065, h916, h918, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h0, h1030, h1065, h916, h918, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h0, h1030, h916, h918, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h916, hlam, p1066_0]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [hlam, p1066_0]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h1063, h1065, hc45, hlam, hphi, p1066_1, u5elo1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h0, h1030, h1065, h916, h918, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h0, h1030, h916, h918, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [hc05, hlam, hphi, p1066_1, u5elo2]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h1027, hlam, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [hlam, p1066_0]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h1065, hc45, hlam, hphi, p1066_1, u5elo2]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h0, h1027, h1030, h916, h918, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [hc05, hlam, hphi, p1066_1, u5elo3]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h1028, hlam, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h1063, hlam, p1066_0]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [hlam, p1066_0]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h0, h1027, h1030, h1063, h916, h918, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h917, hlam, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h1029, hlam, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h1064, hlam, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [h1065, hlam, p1066_1]
                      · have p1066_0 := h1066c.1
                        have p1066_1 := h1066c.2.1
                        have p1066_2 := h1066c.2.2.1
                        have p1066_3 := h1066c.2.2.2
                        linarith only [hlam, p1066_0]
                    · linarith only [h0, h1030, h1065, h918, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h1029, h1064, h916, h918, hlam]
                · linarith only [h0, h1028, h1063, h916, h918, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h1029, h820, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1096 | h1096
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1097 | h1097
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1098 | h1098
                · linarith only [h0, h1027, h1028, h1097, h1098, h916, h918, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h1097, h1098, h918, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h0, h1028, h1097, h916, h918, hc13, hc34, hlam, hphi]
            · linarith only [h0, h1028, h1096, h916, h918, hc13, hc45, hlam, hphi, ht34]
        · linarith only [h0, h1027, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
    · linarith only [h820, h916, h917, hc15, hlam, hphi, u5elo4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1105 | h1105
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1106 | h1106
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1107 | h1107
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1108 | h1108
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1109 | h1109
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1110 | h1110
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1111 | h1111
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1112 | h1112
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1113 | h1113
                    · rcases h5bigk with h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h916, hlam, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1111, hc35, hlam, hphi, p1114_1, u5elo0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h916, hc35, hlam, hphi, p1114_1, u5elo1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h916, hc45, hlam, hphi, p1114_1, u5elo1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hc05, hlam, hphi, p1114_1, u5elo1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hc25, hlam, hphi, p1114_1, u5elo1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hc35, hlam, hphi, p1114_1, u5elo1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hc45, hlam, hphi, p1114_1, u5elo1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1114_1, u5elo2]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1107, hlam, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1107, h1113, hc45, hlam, hphi, ht01, ht0b, ht5b, p1114_1, u1elo1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1106, h1112, hc45, hlam, hphi, ht01, ht0b, ht5b, p1114_1, u1elo1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1114_1, u5elo3]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1108, hlam, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1111, hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hlam, p1114_0]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1106, h1111, h1112, hc45, hlam, hphi, ht01, ht0b, ht5b, p1114_1, u1elo1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1105, hlam, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1109, hlam, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1112, hlam, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [h1113, hlam, p1114_1]
                      · have p1114_0 := h1114c.1
                        have p1114_1 := h1114c.2.1
                        have p1114_2 := h1114c.2.2.1
                        have p1114_3 := h1114c.2.2.2
                        linarith only [hlam, p1114_0]
                    · linarith only [h1106, h1112, h1113, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1141 | h1141
                    · linarith only [h1110, h1112, h1141, hlam]
                    · rcases h5bigk with h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c | h1143c
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [hlam, p1143_0]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h916, hlam, p1143_1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [hc25, hlam, hphi, p1143_1, u5elo0]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1141, h916, hc34, hlam, hphi, ht45, p1143_1, u5elo1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1110, h1112, h916, hc34, hlam, hphi, ht45, p1143_1, u5elo1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [hc05, hlam, hphi, p1143_1, u5elo1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [hlam, p1143_0]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1110, h1112, hc34, hlam, hphi, ht45, p1143_1, u5elo1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1141, hc34, hlam, hphi, ht45, p1143_1, u5elo1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1110, h1112, hc34, hlam, hphi, ht45, p1143_1, u5elo1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1105, h1110, h1112, hc34, hlam, hphi, ht45, p1143_1, u5elo2]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1107, hlam, p1143_1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [hlam, p1143_0]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1107, h1141, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1143_1, u1elo1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1112, hlam, p1143_0]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1105, h1110, h1112, hc34, hlam, hphi, ht45, p1143_1, u5elo3]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1108, hlam, p1143_1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1111, hlam, p1143_0]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [hlam, p1143_0]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1141, hlam, p1143_0]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1105, hlam, p1143_1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1109, hlam, p1143_1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1105, hc25, hlam, hphi, p1143_1, u5elo0]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [h1105, h1106, h820, hc35, hlam, hphi, ht01, ht0b, ht5b, p1143_1, u1elo1]
                      · have p1143_0 := h1143c.1
                        have p1143_1 := h1143c.2.1
                        have p1143_2 := h1143c.2.2.1
                        have p1143_3 := h1143c.2.2.2
                        linarith only [hlam, p1143_0]
                · linarith only [h1110, h1111, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1170 | h1170
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1171 | h1171
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1172 | h1172
                    · rcases h5bigk with h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [hlam, p1173_0]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h916, hlam, p1173_1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h916, hc25, hlam, hphi, p1173_1, u5elo1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h916, hc35, hlam, hphi, p1173_1, u5elo1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h916, hc45, hlam, hphi, p1173_1, u5elo1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [hc05, hlam, hphi, p1173_1, u5elo1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [hlam, p1173_0]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [hc25, hlam, hphi, p1173_1, u5elo1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h1172, hc45, hlam, hphi, p1173_1, u5elo1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [hc45, hlam, hphi, p1173_1, u5elo1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1173_1, u5elo2]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h1107, hlam, p1173_1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [hlam, p1173_0]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h1172, hc45, hlam, hphi, p1173_1, u5elo2]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h1106, h1110, h1170, hc45, hlam, hphi, ht01, ht0b, ht5b, p1173_1, u1elo1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1173_1, u5elo3]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h1108, hlam, p1173_1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h1170, hlam, p1173_0]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [hlam, p1173_0]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h1106, h1110, h1170, hc45, hlam, hphi, ht01, ht0b, ht5b, p1173_1, u1elo1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h1105, hlam, p1173_1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h1109, hlam, p1173_1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h1171, hlam, p1173_1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [h1172, hlam, p1173_1]
                      · have p1173_0 := h1173c.1
                        have p1173_1 := h1173c.2.1
                        have p1173_2 := h1173c.2.2.1
                        have p1173_3 := h1173c.2.2.2
                        linarith only [hlam, p1173_0]
                    · linarith only [h1105, h1110, h1170, h1172, hc35, hlam, hphi, u5elo0]
                  · linarith only [h1105, h1106, h1110, h1170, h1171, h820, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1201 | h1201
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1202 | h1202
                    · rcases h5bigk with h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [hlam, p1203_0]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h916, hlam, p1203_1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [hc25, hlam, hphi, p1203_1, u5elo0]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1170, h916, hc23, hlam, hphi, ht34, ht45, p1203_1, u5elo1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h916, hc45, hlam, hphi, p1203_1, u5elo1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [hc05, hlam, hphi, p1203_1, u5elo1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [hlam, p1203_0]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [hc25, hlam, hphi, p1203_1, u5elo1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1170, hc23, hlam, hphi, ht34, ht45, p1203_1, u5elo1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [hc45, hlam, hphi, p1203_1, u5elo1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1203_1, u5elo2]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1107, hlam, p1203_1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [hlam, p1203_0]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1170, hlam, p1203_1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1106, h1201, hc45, hlam, hphi, ht01, ht0b, ht5b, p1203_1, u1elo1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1203_1, u5elo3]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1108, hlam, p1203_1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1108, hc25, hlam, hphi, ht01, ht0b, ht5b, p1203_1, u1elo2]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [hlam, p1203_0]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1108, hc45, hlam, hphi, ht01, ht0b, ht5b, p1203_1, u1elo2]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1105, hlam, p1203_1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1109, hlam, p1203_1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1201, hlam, p1203_1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [h1202, hlam, p1203_1]
                      · have p1203_0 := h1203c.1
                        have p1203_1 := h1203c.2.1
                        have p1203_2 := h1203c.2.2.1
                        have p1203_3 := h1203c.2.2.2
                        linarith only [hlam, p1203_0]
                    · linarith only [h1105, h1110, h1202, h820, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1230 | h1230
                    · rcases h5bigk with h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [hlam, p1231_0]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h916, hlam, p1231_1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1110, h1201, hc23, hlam, hphi, ht34, ht45, p1231_1, u5elo0]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h916, hc35, hlam, hphi, p1231_1, u5elo1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h916, hc45, hlam, hphi, p1231_1, u5elo1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [hc05, hlam, hphi, p1231_1, u5elo1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [hlam, p1231_0]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1110, h1201, hc23, hlam, hphi, ht34, ht45, p1231_1, u5elo1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [hc35, hlam, hphi, p1231_1, u5elo1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [hc45, hlam, hphi, p1231_1, u5elo1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1105, h1110, h1201, hc23, hlam, hphi, ht34, ht45, p1231_1, u5elo2]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1107, hlam, p1231_1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [hlam, p1231_0]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1170, hlam, p1231_1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1201, hlam, p1231_0]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1105, h1110, h1201, hc23, hc35, hlam, hphi, p1231_1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1108, hlam, p1231_1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1108, hc25, hlam, hphi, ht01, ht0b, ht5b, p1231_1, u1elo2]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [hlam, p1231_0]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1108, h1110, h1201, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1231_1, u1elo2]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1105, hlam, p1231_1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1109, hlam, p1231_1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1110, h1201, h1230, hc23, hc34, hlam, hphi, p1231_1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [h1230, hlam, p1231_1]
                      · have p1231_0 := h1231c.1
                        have p1231_1 := h1231c.2.1
                        have p1231_2 := h1231c.2.2.1
                        have p1231_3 := h1231c.2.2.2
                        linarith only [hlam, p1231_0]
                    · linarith only [h1105, h1106, h1110, h1230, h820, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
            · linarith only [h1105, h1109, h820, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1259 | h1259
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1260 | h1260
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1261 | h1261
                · linarith only [h1107, h1108, h1261, h916, hc01, hlam, hphi, u1elo1]
                · linarith only [h1260, h1261, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1264 | h1264
                · linarith only [h1108, h1260, h1264, hc13, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1266 | h1266
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1267 | h1267
                    · rcases h5bigk with h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [hlam, p1268_0]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h916, hlam, p1268_1]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [hc25, hlam, hphi, p1268_1, u5elo0]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1108, h916, hlam, p1268_1]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1108, h916, hc45, hlam, hphi, p1268_1, u5elo3]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1108, hc05, hlam, hphi, p1268_1, u5elo3]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [hlam, p1268_0]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1108, hc25, hlam, hphi, p1268_1, u5elo3]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1108, hlam, p1268_0]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1108, hc45, hlam, hphi, p1268_1, u5elo3]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1268_1, u5elo2]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1107, hlam, p1268_1]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [hlam, p1268_0]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1264, hlam, p1268_1]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1106, h1266, hc45, hlam, hphi, ht01, ht0b, ht5b, p1268_1, u1elo1]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1268_1, u5elo3]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [hc15, hlam, hphi, p1268_1, u5elo3]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [hc25, hlam, hphi, p1268_1, u5elo3]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [hlam, p1268_0]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [hc45, hlam, hphi, p1268_1, u5elo3]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1105, hlam, p1268_1]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1259, hlam, p1268_1]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1266, hlam, p1268_1]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [h1267, hlam, p1268_1]
                      · have p1268_0 := h1268c.1
                        have p1268_1 := h1268c.2.1
                        have p1268_2 := h1268c.2.2.1
                        have p1268_3 := h1268c.2.2.2
                        linarith only [hlam, p1268_0]
                    · linarith only [h1105, h1260, h1267, hc23, hlam, hphi, ht34, ht45, u5elo0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1295 | h1295
                    · rcases h5bigk with h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c | h1296c
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [hlam, p1296_0]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h916, hlam, p1296_1]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1108, h1260, h1266, h916, hc23, hlam, hphi, ht34, ht45, p1296_1, u5elo3]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1108, h916, hlam, p1296_1]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1108, h1260, h1266, h916, hc23, hlam, hphi, ht34, ht45, p1296_1, u5elo3]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1108, hc05, hlam, hphi, p1296_1, u5elo3]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [hlam, p1296_0]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1108, h1260, h1266, hc23, hlam, hphi, ht34, ht45, p1296_1, u5elo3]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1108, hlam, p1296_0]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1108, h1260, h1266, hc23, hlam, hphi, ht34, ht45, p1296_1, u5elo3]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1105, h1260, h1266, hc23, hlam, hphi, ht34, ht45, p1296_1, u5elo2]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1107, hlam, p1296_1]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [hlam, p1296_0]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1264, hlam, p1296_1]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1266, hlam, p1296_0]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1105, h1260, h1266, hc23, hlam, hphi, ht34, ht45, p1296_1, u5elo3]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [hc15, hlam, hphi, p1296_1, u5elo3]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [hc25, hlam, hphi, p1296_1, u5elo3]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [hlam, p1296_0]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1260, h1266, hc23, hlam, hphi, ht34, ht45, p1296_1, u5elo3]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1105, hlam, p1296_1]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1259, hlam, p1296_1]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1105, h1106, h1260, h1266, h820, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1296_1, u1elo1]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [h1295, hlam, p1296_1]
                      · have p1296_0 := h1296c.1
                        have p1296_1 := h1296c.2.1
                        have p1296_2 := h1296c.2.2.1
                        have p1296_3 := h1296c.2.2.2
                        linarith only [hlam, p1296_0]
                    · linarith only [h1105, h1106, h1260, h1295, h820, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
            · linarith only [h1105, h1259, h820, hlam]
        · linarith only [h1105, h1106, h1107, h820, hc45, hlam, hphi, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1325 | h1325
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1326 | h1326
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1327 | h1327
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1328 | h1328
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1329 | h1329
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1330 | h1330
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1331 | h1331
                    · rcases h5bigk with h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c | h1332c
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [hlam, p1332_0]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h916, hlam, p1332_1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [hc25, hlam, hphi, p1332_1, u5elo0]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1331, hc45, hlam, hphi, p1332_1, u5elo0]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h916, hc45, hlam, hphi, p1332_1, u5elo1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [hc05, hlam, hphi, p1332_1, u5elo1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [hlam, p1332_0]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1329, h1331, hc45, hlam, hphi, p1332_1, u5elo1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1331, hc45, hlam, hphi, p1332_1, u5elo1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [hc45, hlam, hphi, p1332_1, u5elo1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1332_1, u5elo2]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1325, hlam, p1332_1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [hlam, p1332_0]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1325, h1331, hc45, hlam, hphi, ht01, ht0b, ht5b, p1332_1, u1elo1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1106, h1325, h1328, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1332_1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1332_1, u5elo3]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1326, hlam, p1332_1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1329, hlam, p1332_0]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [hlam, p1332_0]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1106, h1325, h1328, h1329, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1332_1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1105, hlam, p1332_1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1327, hlam, p1332_1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1330, hlam, p1332_1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [h1331, hlam, p1332_1]
                      · have p1332_0 := h1332c.1
                        have p1332_1 := h1332c.2.1
                        have p1332_2 := h1332c.2.2.1
                        have p1332_3 := h1332c.2.2.2
                        linarith only [hlam, p1332_0]
                    · rcases h5bigk with h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [hlam, p1358_0]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h916, hlam, p1358_1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [hc25, hlam, hphi, p1358_1, u5elo0]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h916, hc35, hlam, hphi, p1358_1, u5elo1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1331, h916, hc34, hlam, hphi, ht45, p1358_1, u5elo1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [hc05, hlam, hphi, p1358_1, u5elo1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [hlam, p1358_0]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1330, h1331, hc34, hlam, hphi, ht45, p1358_1, u5elo1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [hc35, hlam, hphi, p1358_1, u5elo1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1331, hc34, hlam, hphi, ht45, p1358_1, u5elo1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1105, h1331, hc34, hlam, hphi, ht45, p1358_1, u5elo2]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1325, hlam, p1358_1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [hlam, p1358_0]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1106, h1325, h1328, h1331, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1358_1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1106, h1325, h1328, h1331, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1358_1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1105, h1331, hc34, hlam, hphi, ht45, p1358_1, u5elo3]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1326, hlam, p1358_1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1329, hlam, p1358_0]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [hlam, p1358_0]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1331, hlam, p1358_0]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1105, hlam, p1358_1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1327, hlam, p1358_1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1330, hlam, p1358_1]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [h1105, hc35, hlam, hphi, p1358_1, u5elo0]
                      · have p1358_0 := h1358c.1
                        have p1358_1 := h1358c.2.1
                        have p1358_2 := h1358c.2.2.1
                        have p1358_3 := h1358c.2.2.2
                        linarith only [hlam, p1358_0]
                  · linarith only [h1105, h1106, h1330, h820, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · linarith only [h1328, h1329, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1386 | h1386
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1387 | h1387
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1388 | h1388
                    · rcases h5bigk with h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [hlam, p1389_0]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h916, hlam, p1389_1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h916, hc25, hlam, hphi, p1389_1, u5elo1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1388, h916, hc45, hlam, hphi, p1389_1, u5elo1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h916, hc45, hlam, hphi, p1389_1, u5elo1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [hc05, hlam, hphi, p1389_1, u5elo1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [hlam, p1389_0]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1386, h1388, hc45, hlam, hphi, p1389_1, u5elo1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1388, hc45, hlam, hphi, p1389_1, u5elo1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [hc45, hlam, hphi, p1389_1, u5elo1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1389_1, u5elo2]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1325, hlam, p1389_1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [hlam, p1389_0]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1106, h1325, h1328, h1388, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1389_1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1106, h1325, h1328, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1389_1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1389_1, u5elo3]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1326, hlam, p1389_1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1386, hlam, p1389_0]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [hlam, p1389_0]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1106, h1325, h1328, h1386, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1389_1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1105, hlam, p1389_1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1327, hlam, p1389_1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1387, hlam, p1389_1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [h1388, hlam, p1389_1]
                      · have p1389_0 := h1389c.1
                        have p1389_1 := h1389c.2.1
                        have p1389_2 := h1389c.2.2.1
                        have p1389_3 := h1389c.2.2.2
                        linarith only [hlam, p1389_0]
                    · linarith only [h1106, h1328, h1388, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1105, h1106, h1387, h820, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1417 | h1417
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1418 | h1418
                    · rcases h5bigk with h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h916, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hc25, hlam, hphi, p1419_1, u5elo0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1386, h916, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1419_1, u1elo4]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h916, hc45, hlam, hphi, p1419_1, u5elo1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hc05, hlam, hphi, p1419_1, u5elo1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1386, hc23, hlam, hphi, ht34, ht45, p1419_1, u5elo1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1386, hc23, hlam, hphi, ht34, ht45, p1419_1, u5elo1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hc45, hlam, hphi, p1419_1, u5elo1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1419_1, u5elo2]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1325, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1386, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1106, h1325, h1328, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1419_1, u5elo3]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1326, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1326, hc25, hlam, hphi, ht01, ht0b, ht5b, p1419_1, u1elo2]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hlam, p1419_0]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1326, hc45, hlam, hphi, ht01, ht0b, ht5b, p1419_1, u1elo2]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1105, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1327, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1417, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [h1418, hlam, p1419_1]
                      · have p1419_0 := h1419c.1
                        have p1419_1 := h1419c.2.1
                        have p1419_2 := h1419c.2.2.1
                        have p1419_3 := h1419c.2.2.2
                        linarith only [hlam, p1419_0]
                    · linarith only [h1106, h1328, h1418, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1105, h1106, h1325, h1417, h820, h916, hc01, hlam, hphi, u1elo3]
            · linarith only [h1105, h1327, h820, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1448 | h1448
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1449 | h1449
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1450 | h1450
                · linarith only [h1325, h1326, h1450, h916, hc01, hlam, hphi, u1elo1]
                · linarith only [h1106, h1449, h1450, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1453 | h1453
                · linarith only [h1326, h1449, h1453, hc13, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1455 | h1455
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1456 | h1456
                    · rcases h5bigk with h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [hlam, p1457_0]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h916, hlam, p1457_1]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [hc25, hlam, hphi, p1457_1, u5elo0]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h1326, h916, hlam, p1457_1]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [hc45, hlam, hphi, p1457_1, u5elo0]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [hc05, hlam, hphi, p1457_1, u5elo1]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [hlam, p1457_0]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h1326, h1453, hc23, hlam, hphi, ht34, ht45, p1457_1, u5elo3]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h1326, hlam, p1457_0]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h1326, hc45, hlam, hphi, p1457_1, u5elo3]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1457_1, u5elo2]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h1325, hlam, p1457_1]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [hlam, p1457_0]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h1453, hlam, p1457_1]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h1106, h1325, h1449, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1457_1]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h916, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1457_1, u5elo3]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [hc15, hlam, hphi, p1457_1, u5elo3]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [hc25, hlam, hphi, p1457_1, u5elo3]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [hlam, p1457_0]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [hc45, hlam, hphi, p1457_1, u5elo3]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h1105, hlam, p1457_1]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h1448, hlam, p1457_1]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h1455, hlam, p1457_1]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [h1456, hlam, p1457_1]
                      · have p1457_0 := h1457c.1
                        have p1457_1 := h1457c.2.1
                        have p1457_2 := h1457c.2.2.1
                        have p1457_3 := h1457c.2.2.2
                        linarith only [hlam, p1457_0]
                    · linarith only [h1106, h1449, h1456, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1105, h1106, h1325, h1455, h820, h916, hc01, hlam, hphi, u1elo3]
            · linarith only [h1105, h1448, h820, hlam]
        · linarith only [h0, h1325, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1487 | h1487
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1488 | h1488
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1489 | h1489
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1490 | h1490
            · linarith only [h1105, h1487, h1490, h820, hc01, hlam, hphi, u1elo1]
            · linarith only [h1490, h820, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1493 | h1493
            · linarith only [h1105, h1493, h820, hc01, hlam, hphi, u1elo3]
            · linarith only [h1493, h820, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
        · linarith only [h1487, h1488, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1497 | h1497
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1498 | h1498
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1499 | h1499
            · linarith only [h1105, h1499, h820, hc01, hlam, hphi, u1elo3]
            · linarith only [h1499, h820, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1502 | h1502
            · linarith only [h1105, h1502, h820, hc01, hlam, hphi, u1elo3]
            · linarith only [h1502, h820, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
        · linarith only [h0, h1497, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 3012000 in
set_option maxHeartbeats 3012000 in
theorem r1l7_11_25_L_0_M_LI_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h820 | h820
  · exact r1l7_11_25_L_0_M_LI_x1_x0 m hb1 hb5 h0 h820
  · exact r1l7_11_25_L_0_M_LI_x1_x1 m hb1 hb5 h0 h820

end R2N4
