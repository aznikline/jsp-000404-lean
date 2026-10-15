import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_54S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h952 | h952
  · rcases m.htr 0 1 5 (by decide) (by decide) with h953 | h953
    · rcases m.htr 1 2 3 (by decide) (by decide) with h954 | h954
      · linarith only [h0, h1, h954, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h956 | h956
        · rcases m.htr 1 2 5 (by decide) (by decide) with h957 | h957
          · rcases m.htr 1 3 4 (by decide) (by decide) with h958 | h958
            · rcases m.htr 1 3 5 (by decide) (by decide) with h959 | h959
              · rcases m.htr 1 4 5 (by decide) (by decide) with h960 | h960
                · rcases m.htr 2 3 4 (by decide) (by decide) with h961 | h961
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h962 | h962
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h963 | h963
                      · linarith only [h0, h1, h954, h956, h961, h963, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1, h954, h956, h960, h963, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1, h954, h962, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h1, h954, h961, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h968 | h968
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h969 | h969
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h970 | h970
                      · linarith only [h0, h1, h956, h968, h970, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases h1bigk with h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c | h972c
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [hlam, p972_0]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h1, h954, h957, h969, h970, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p972_1]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h1, hlam, p972_0]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h1, h954, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p972_1]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h1, h954, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p972_1]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h0, hlam, p972_0]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [hlam, p972_0]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h954, hlam, p972_0]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h0, h1, h954, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p972_1]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h0, h1, h954, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p972_1]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h954, hc01, hc23, hlam, hphi, ht12, p972_1]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h954, hc12, hc23, hlam, hphi, p972_1]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [hlam, p972_0]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          rcases p972_3 (m.d 0 1) (by simp) with h986 | h986
                          · linarith only [h1, h986, hlam]
                          · linarith only [h952, h986, hlam]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          rcases p972_3 (m.d 0 1) (by simp) with h989 | h989
                          · linarith only [h1, h989, hlam]
                          · linarith only [h953, h989, hlam]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h952, hlam, p972_0]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h956, hlam, p972_1]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h958, hlam, p972_0]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [hlam, p972_0]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h960, hlam, p972_1]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h953, hlam, p972_0]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h957, hlam, p972_1]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h959, hlam, p972_0]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [h956, h968, hc34, hlam, hphi, ht45, p972_1, u5elo1]
                        · have p972_0 := h972c.1
                          have p972_1 := h972c.2.1
                          have p972_2 := h972c.2.2.1
                          have p972_3 := h972c.2.2.2
                          linarith only [hlam, p972_0]
                    · linarith only [h1, h954, h969, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h1, h954, h956, h968, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h0, h1, h956, h959, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h0, h1, h956, h958, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h956, h957, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1007 | h1007
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1008 | h1008
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1009 | h1009
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1010 | h1010
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1011 | h1011
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1012 | h1012
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1013 | h1013
                      · rcases h1bigk with h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1007, h1012, h1013, hc01, hc45, hlam, hphi, ht0b, ht5b, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1, h1007, h1012, h1013, h954, h956, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1, h954, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h0, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h954, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h956, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h956, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h954, hc01, hc23, hlam, hphi, ht12, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h954, hc12, hc23, hlam, hphi, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1007, h1012, h1013, h954, h956, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          rcases p1014_3 (m.d 0 1) (by simp) with h1029 | h1029
                          · linarith only [h1, h1029, hlam]
                          · linarith only [h1029, h953, hlam]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h952, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1007, h1012, h1013, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1008, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1, h1007, h1012, h1013, h952, h954, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h953, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1007, hlam, p1014_1]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1009, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [h1010, hlam, p1014_0]
                        · have p1014_0 := h1014c.1
                          have p1014_1 := h1014c.2.1
                          have p1014_2 := h1014c.2.2.1
                          have p1014_3 := h1014c.2.2.2
                          linarith only [hlam, p1014_0]
                      · linarith only [h1, h1010, h1013, h952, h954, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h1, h1012, h954, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1, h1007, h1011, h952, h954, h956, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h1007, h1010, h956, hc25, hlam, hphi, u5elo4]
              · linarith only [h1, h1007, h1009, h952, h956, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
            · linarith only [h1, h1007, h1008, h952, h956, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1048 | h1048
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1049 | h1049
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1050 | h1050
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1051 | h1051
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1052 | h1052
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1053 | h1053
                      · rcases h1bigk with h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c | h1054c
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1054_1]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h1, hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h1, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1054_1]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h1, h954, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1054_1]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h0, hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h954, hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h956, hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h1007, hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h954, hc01, hc23, hlam, hphi, ht12, p1054_1]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h954, hc12, hc23, hlam, hphi, p1054_1]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h1048, h1053, h954, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1054_1]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h1007, h954, hc12, hc23, hlam, hphi, p1054_1]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h952, hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h952, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1054_1]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h1048, hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h1, h1007, h952, h954, hc12, hc23, hlam, hphi, p1054_1]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h953, hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1054_1, u5elo1]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h1049, hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [h1050, hlam, p1054_0]
                        · have p1054_0 := h1054c.1
                          have p1054_1 := h1054c.2.1
                          have p1054_2 := h1054c.2.2.1
                          have p1054_3 := h1054c.2.2.2
                          linarith only [hlam, p1054_0]
                      · linarith only [h1, h1050, h1053, h952, h954, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h1, h1050, h1052, h952, h954, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h1, h1050, h1051, h952, h954, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1083 | h1083
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1084 | h1084
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1085 | h1085
                      · linarith only [h1048, h1050, h1085, hlam]
                      · rcases h1bigk with h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1087_1]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h1, hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h1, h954, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1087_1]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h1, h954, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1087_1]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h0, hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h954, hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h956, hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h1007, hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h954, hc01, hc23, hlam, hphi, ht12, p1087_1]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h954, hc12, hc23, hlam, hphi, p1087_1]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h954, h956, hc12, hc23, hlam, hphi, p1087_1]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h1007, h954, hc12, hc23, hlam, hphi, p1087_1]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h952, hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h952, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1087_1]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h1048, hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h1050, hlam, p1087_1]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h953, hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p1087_1, u5elo1]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h1049, hlam, p1087_0]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [h1, h953, h954, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1087_1]
                        · have p1087_0 := h1087c.1
                          have p1087_1 := h1087c.2.1
                          have p1087_2 := h1087c.2.2.1
                          have p1087_3 := h1087c.2.2.2
                          linarith only [hlam, p1087_0]
                    · linarith only [h1, h1084, h954, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1, h1050, h1083, h953, h954, h956, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h1049, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h1, h1048, h952, h956, hc12, hc34, hlam, hphi, ht23]
    · linarith only [h952, h953, hc14, hlam, hphi, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1118 | h1118
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1119 | h1119
      · linarith only [h0, h1, h1119, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1121 | h1121
        · linarith only [h0, h1121, h952, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1123 | h1123
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1124 | h1124
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1125 | h1125
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1126 | h1126
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1127 | h1127
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1128 | h1128
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1129 | h1129
                      · rcases h1bigk with h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1124, h952, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1130_1]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1, hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h952, hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1119, h1124, h952, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1130_1]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h0, hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1119, hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1121, hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h0, h1119, h1124, h952, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1130_1]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1119, hc01, hc23, hlam, hphi, ht12, p1130_1]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1119, hc12, hc23, hlam, hphi, p1130_1]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h0, h1119, h952, hc12, hc23, hlam, hphi, p1130_1]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          rcases p1130_3 (m.d 0 1) (by simp) with h1145 | h1145
                          · linarith only [h1, h1145, hlam]
                          · linarith only [h1118, h1145, hlam]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h0, h1123, h1128, h1129, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1130_1]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1121, h1123, h1128, h1129, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1130_1]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1124, hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          rcases p1130_3 (m.d 0 1) (by simp) with h1152 | h1152
                          · linarith only [h1152, h952, hlam]
                          · linarith only [h1118, h1152, hlam]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1118, hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1123, hlam, p1130_1]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1125, hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [h1126, hlam, p1130_0]
                        · have p1130_0 := h1130c.1
                          have p1130_1 := h1130c.2.1
                          have p1130_2 := h1130c.2.2.1
                          have p1130_3 := h1130c.2.2.2
                          linarith only [hlam, p1130_0]
                      · rcases h1bigk with h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1119, h1124, h952, hc12, hc23, hlam, hphi, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h952, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1119, h1124, h952, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h0, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1119, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1121, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h0, h1119, h1124, h952, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1119, hc01, hc23, hlam, hphi, ht12, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1119, hc12, hc23, hlam, hphi, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h0, h1119, h952, hc12, hc23, hlam, hphi, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1119, h1126, h1129, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h0, h1123, h1126, h1129, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1121, h1123, h1126, h1127, h1129, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1124, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1121, h1126, h1127, h1129, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1118, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1123, hlam, p1160_1]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1125, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [h1126, hlam, p1160_0]
                        · have p1160_0 := h1160c.1
                          have p1160_1 := h1160c.2.1
                          have p1160_2 := h1160c.2.2.1
                          have p1160_3 := h1160c.2.2.2
                          linarith only [hlam, p1160_0]
                    · linarith only [h1, h1119, h1128, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h1119, h1123, h1124, h1127, h952, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h0, h1123, h1126, h952, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
              · linarith only [h0, h1123, h1124, h1125, h952, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
            · linarith only [h0, h1, h1123, h1124, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1191 | h1191
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1192 | h1192
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1193 | h1193
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1194 | h1194
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1195 | h1195
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1196 | h1196
                      · rcases h1bigk with h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1191, h952, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1197_1]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1, hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h952, hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1119, h1123, h1191, h952, hc12, hc23, hlam, hphi, p1197_1]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h0, hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1119, hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1121, hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1123, hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1119, hc01, hc23, hlam, hphi, ht12, p1197_1]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1119, hc12, hc23, hlam, hphi, p1197_1]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1118, h1119, h1123, h952, hc12, hc23, hlam, hphi, p1197_1]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1119, h1123, hc12, hc23, hlam, hphi, p1197_1]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1118, h1123, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1197_1]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1121, hc12, hc24, hlam, hphi, p1197_1]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1191, hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1119, h1123, h1191, hc12, hc23, hlam, hphi, p1197_1]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1118, hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1118, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1197_1]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1192, hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [h1193, hlam, p1197_0]
                        · have p1197_0 := h1197c.1
                          have p1197_1 := h1197c.2.1
                          have p1197_2 := h1197c.2.2.1
                          have p1197_3 := h1197c.2.2.2
                          linarith only [hlam, p1197_0]
                      · rcases h1bigk with h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c | h1223c
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1119, h1191, h952, hc12, hc23, hlam, hphi, p1223_1]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1, hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h952, hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1119, h1191, h1193, h1196, h952, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1223_1]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h0, hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1119, hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1121, hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1123, hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1119, hc01, hc23, hlam, hphi, ht12, p1223_1]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1119, hc12, hc23, hlam, hphi, p1223_1]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1118, h1119, h1193, h1196, h952, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1223_1]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1119, h1193, h1196, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1223_1]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1118, h1193, h1196, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1223_1]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1121, h1194, hc12, hc23, hlam, hphi, p1223_1]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1191, hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1121, h1193, h1194, h1196, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1223_1]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1118, hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1118, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1223_1]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1192, hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [h1193, hlam, p1223_0]
                        · have p1223_0 := h1223c.1
                          have p1223_1 := h1223c.2.1
                          have p1223_2 := h1223c.2.2.1
                          have p1223_3 := h1223c.2.2.2
                          linarith only [hlam, p1223_0]
                    · linarith only [h1118, h1121, h1193, h1194, h1195, h952, hc45, hlam, hphi, u5elo3]
                  · linarith only [h1118, h1119, h1123, h1191, h1194, h952, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1118, h1123, h1193, h952, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h1118, h1123, h1191, h1192, h952, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h1, h1118, h1123, h1191, hc12, hc34, hlam, hphi, ht23]
    · linarith only [h0, h1118, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_21_15_H_I_L_0_x0_x0 m hb1 hb5 h0 h1
  · exact r1l7_21_15_H_I_L_0_x0_x1 m hb1 hb5 h0 h1

set_option maxHeartbeats 4660000 in
set_option maxHeartbeats 4660000 in
theorem r1l7_21_15_H_I_L_0_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1255 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1256 | h1256
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1257 | h1257
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1258 | h1258
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1259 | h1259
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1260 | h1260
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1261 | h1261
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1262 | h1262
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1263 | h1263
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1264 | h1264
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1265 | h1265
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1266 | h1266
                      · linarith only [h0, h1255, h1258, h1264, h1266, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h1255, h1261, h1263, h1266, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h1255, h1262, h1265, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1255, h1261, h1264, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1271 | h1271
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1272 | h1272
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1273 | h1273
                      · linarith only [h1258, h1259, h1263, h1271, h1273, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h1bigk with h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [hlam, p1275_0]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h0, hlam, p1275_0]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1275_1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h0, h1259, h1271, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1275_1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1275_1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [hc01, hc12, hlam, hphi, p1275_1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [hlam, p1275_0]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1258, h1272, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1275_1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          rcases p1275_3 (m.d 0 1) (by simp) with h1284 | h1284
                          · linarith only [h0, h1284, hlam]
                          · linarith only [h1256, h1284, hlam]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          rcases p1275_3 (m.d 0 1) (by simp) with h1287 | h1287
                          · linarith only [h0, h1287, hlam]
                          · linarith only [h1257, h1287, hlam]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1255, hlam, p1275_0]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1258, hlam, p1275_1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [hlam, p1275_0]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1255, h1259, h1271, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1275_1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h0, h1255, h1259, h1263, h1271, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1275_1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1256, hlam, p1275_0]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1259, hlam, p1275_1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1261, hlam, p1275_0]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [hlam, p1275_0]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1263, hlam, p1275_1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1257, hlam, p1275_0]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1260, hlam, p1275_1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1262, hlam, p1275_0]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [h1259, h1271, hc34, hlam, hphi, ht45, p1275_1, u5elo1]
                        · have p1275_0 := h1275c.1
                          have p1275_1 := h1275c.2.1
                          have p1275_2 := h1275c.2.2.1
                          have p1275_3 := h1275c.2.2.2
                          linarith only [hlam, p1275_0]
                    · linarith only [h0, h1255, h1262, h1272, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1255, h1261, h1271, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h1261, h1262, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1308 | h1308
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1309 | h1309
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1310 | h1310
                  · linarith only [h1258, h1261, h1308, h1310, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1312 | h1312
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1313 | h1313
                      · rcases h1bigk with h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [hlam, p1314_0]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h0, hlam, p1314_0]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h0, h1258, h1312, h1313, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h0, h1258, h1261, h1312, h1313, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [hc01, hc12, hlam, hphi, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [hlam, p1314_0]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1258, h1312, h1313, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1258, h1261, h1312, h1313, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          rcases p1314_3 (m.d 0 1) (by simp) with h1324 | h1324
                          · linarith only [h0, h1324, hlam]
                          · linarith only [h1257, h1324, hlam]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1255, hlam, p1314_0]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1258, hlam, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [hlam, p1314_0]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1261, hlam, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1256, h1260, h1261, h1312, h1313, hc01, hc45, hlam, hphi, ht0b, ht5b, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1256, hlam, p1314_0]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1259, hlam, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1256, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [hlam, p1314_0]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h0, h1256, h1260, h1312, h1313, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1257, hlam, p1314_0]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1260, hlam, p1314_1]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1308, hlam, p1314_0]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [h1309, hlam, p1314_0]
                        · have p1314_0 := h1314c.1
                          have p1314_1 := h1314c.2.1
                          have p1314_2 := h1314c.2.2.1
                          have p1314_3 := h1314c.2.2.2
                          linarith only [hlam, p1314_0]
                      · linarith only [h1261, h1313, hc13, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h1261, h1308, h1312, hc23, hc34, hlam, hphi]
                · linarith only [h1261, h1308, h1309, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1345 | h1345
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1346 | h1346
                  · linarith only [h1258, h1308, h1346, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1348 | h1348
                    · linarith only [h1258, h1308, h1348, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1350 | h1350
                      · rcases h1bigk with h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [hlam, p1351_0]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h0, hlam, p1351_0]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [hc01, hc12, hlam, hphi, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [hlam, p1351_0]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          rcases p1351_3 (m.d 0 1) (by simp) with h1359 | h1359
                          · linarith only [h0, h1359, hlam]
                          · linarith only [h1255, h1359, hlam]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          rcases p1351_3 (m.d 0 1) (by simp) with h1363 | h1363
                          · linarith only [h0, h1363, hlam]
                          · linarith only [h1257, h1363, hlam]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1255, hlam, p1351_0]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1258, hlam, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [hlam, p1351_0]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1261, hlam, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1308, hlam, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1256, hlam, p1351_0]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1259, hlam, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1256, h1258, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [hlam, p1351_0]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h0, h1256, h1260, h1348, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1257, hlam, p1351_0]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1260, hlam, p1351_1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1258, hc23, hlam, hphi, ht34, ht45, p1351_1, u5elo1]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [h1345, hlam, p1351_0]
                        · have p1351_0 := h1351c.1
                          have p1351_1 := h1351c.2.1
                          have p1351_2 := h1351c.2.2.1
                          have p1351_3 := h1351c.2.2.2
                          linarith only [hlam, p1351_0]
                      · linarith only [h1258, h1261, h1350, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1382 | h1382
                  · linarith only [h1258, h1261, h1382, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1384 | h1384
                    · linarith only [h1258, h1308, h1384, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1386 | h1386
                      · rcases h1bigk with h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c | h1387c
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [hlam, p1387_0]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h0, hlam, p1387_0]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h0, h1258, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h0, h1258, h1261, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [hc01, hc12, hlam, hphi, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [hlam, p1387_0]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          rcases p1387_3 (m.d 0 1) (by simp) with h1395 | h1395
                          · linarith only [h0, h1395, hlam]
                          · linarith only [h1255, h1395, hlam]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          rcases p1387_3 (m.d 0 1) (by simp) with h1398 | h1398
                          · linarith only [h0, h1398, hlam]
                          · linarith only [h1256, h1398, hlam]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          rcases p1387_3 (m.d 0 1) (by simp) with h1401 | h1401
                          · linarith only [h0, h1401, hlam]
                          · linarith only [h1257, h1401, hlam]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h1255, hlam, p1387_0]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h1258, hlam, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [hlam, p1387_0]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h1261, hlam, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h1308, hlam, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h1256, hlam, p1387_0]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h1259, hlam, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h1257, h1258, h1345, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [hlam, p1387_0]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h1345, hlam, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h1257, hlam, p1387_0]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h1260, hlam, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h0, h1257, h1258, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [h0, h1257, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1387_1]
                        · have p1387_0 := h1387c.1
                          have p1387_1 := h1387c.2.1
                          have p1387_2 := h1387c.2.2.1
                          have p1387_3 := h1387c.2.2.2
                          linarith only [hlam, p1387_0]
                      · linarith only [h1258, h1261, h1386, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h0, h1260, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h0, h1256, h1259, hlam]
      · linarith only [h0, h1255, h1258, hlam]
    · linarith only [h1255, h1257, hc13, hlam, hphi, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1424 | h1424
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1425 | h1425
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1426 | h1426
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1427 | h1427
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1428 | h1428
            · linarith only [h1255, h1256, h1428, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1430 | h1430
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1431 | h1431
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1432 | h1432
                  · linarith only [h1255, h1256, h1428, h1430, h1432, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1434 | h1434
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1435 | h1435
                      · rcases h1bigk with h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c | h1436c
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h0, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1256, h1425, h1428, h1434, h1435, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1256, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1256, h1428, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hc01, hc12, hlam, hphi, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1425, h1434, h1435, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1255, h1256, h1425, h1434, h1435, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          rcases p1436_3 (m.d 0 1) (by simp) with h1446 | h1446
                          · linarith only [h0, h1446, hlam]
                          · linarith only [h1424, h1446, hlam]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1255, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1425, hlam, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1428, hlam, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1255, h1427, h1434, h1435, hc01, hc45, hlam, hphi, ht0b, ht5b, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hc01, hc14, hlam, hphi, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1426, hlam, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1425, h1428, h1434, h1435, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          rcases p1436_3 (m.d 0 1) (by simp) with h1458 | h1458
                          · linarith only [h1256, h1458, hlam]
                          · linarith only [h1424, h1458, hlam]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1424, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1427, hlam, p1436_1]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1430, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [h1431, hlam, p1436_0]
                        · have p1436_0 := h1436c.1
                          have p1436_1 := h1436c.2.1
                          have p1436_2 := h1436c.2.2.1
                          have p1436_3 := h1436c.2.2.2
                          linarith only [hlam, p1436_0]
                      · linarith only [h1255, h1256, h1425, h1428, h1434, h1435, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                    · linarith only [h1255, h1256, h1428, h1430, h1434, hc23, hc34, hlam, hphi]
                · linarith only [h1255, h1256, h1431, hc13, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1469 | h1469
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1470 | h1470
                  · linarith only [h1256, h1424, h1425, h1428, h1430, h1470, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1472 | h1472
                    · linarith only [h1425, h1430, h1472, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1474 | h1474
                      · rcases h1bigk with h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c | h1475c
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [hlam, p1475_0]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h0, hlam, p1475_0]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1256, h1425, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1256, hlam, p1475_0]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1256, h1425, h1428, h1430, hc23, hc34, hlam, hphi, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [hc01, hc12, hlam, hphi, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [hlam, p1475_0]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          rcases p1475_3 (m.d 0 1) (by simp) with h1483 | h1483
                          · linarith only [h0, h1483, hlam]
                          · linarith only [h1255, h1483, hlam]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1256, h1424, h1425, h1430, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          rcases p1475_3 (m.d 0 1) (by simp) with h1487 | h1487
                          · linarith only [h0, h1487, hlam]
                          · linarith only [h1424, h1487, hlam]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1255, hlam, p1475_0]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1425, hlam, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [hlam, p1475_0]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1428, hlam, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1430, hlam, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1424, h1425, h1430, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1426, hlam, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1425, h1428, hc23, hc34, hlam, hphi, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [hlam, p1475_0]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1425, h1428, h1430, hc23, hc34, hlam, hphi, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1424, hlam, p1475_0]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1427, hlam, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1424, h1425, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1475_1]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [h1469, hlam, p1475_0]
                        · have p1475_0 := h1475c.1
                          have p1475_1 := h1475c.2.1
                          have p1475_2 := h1475c.2.2.1
                          have p1475_3 := h1475c.2.2.2
                          linarith only [hlam, p1475_0]
                      · linarith only [h1256, h1424, h1428, h1469, h1474, hlam]
                · linarith only [h1256, h1424, h1427, h1469, hc25, hlam, hphi, u5elo4]
          · linarith only [h0, h1255, h1425, h1427, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1508 | h1508
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1509 | h1509
            · linarith only [h0, h1255, h1426, h1509, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1511 | h1511
              · linarith only [h0, h1255, h1426, h1511, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1513 | h1513
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1514 | h1514
                  · linarith only [h0, h1424, h1425, h1426, h1509, h1511, h1514, hlam]
                  · linarith only [h0, h1424, h1425, h1426, h1511, h1514, hc23, hc34, hlam, hphi]
                · linarith only [h0, h1424, h1425, h1426, h1511, h1513, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h0, h1508, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
      · linarith only [h0, h1255, h1425, hlam]
    · linarith only [h1255, h1424, hc13, hlam, hphi, ht34, ht45, u5elo1]

end R2N4
