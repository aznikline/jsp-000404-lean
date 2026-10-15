import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S32
import Jsp000404.R1LeavesN7_2S33
import Jsp000404.R1LeavesN7_2S34

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h22731 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h22732 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h22733 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h22734 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h23282 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 2 3 5 (by decide) (by decide) with h24005 | h24005
  · rcases m.htr 2 4 5 (by decide) (by decide) with h24006 | h24006
    · linarith only [h16915, h20411, h22734, h23282, h24005, h24006, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
    · linarith only [h23282, h24005, h24006, hlam]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h24009 | h24009
    · linarith only [h16915, h22734, h24009, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h24011 | h24011
      · linarith only [h16915, h20411, h22734, h24011, hlam]
      · rcases h0bigk with h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c | h24013c
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [hlam, p24013_0]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h0, hlam, p24013_1]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h14396, hlam, p24013_0]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h16915, hlam, p24013_1]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h18815, hlam, p24013_1]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          rcases p24013_3 (m.d 0 1) (by simp) with h24019 | h24019
          · linarith only [h0, h24019, hlam]
          · rcases p24013_3 (m.d 0 2) (by simp) with h24021 | h24021
            · rcases p24013_3 (m.d 0 3) (by simp) with h24022 | h24022
              · linarith only [h20408, h24022, hlam]
              · linarith only [h14396, h24022, hlam]
            · linarith only [h0, h24021, hlam]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [hlam, p24013_0]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h0, h20411, h23282, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24013_1]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          rcases p24013_3 (m.d 0 1) (by simp) with h24028 | h24028
          · linarith only [h0, h24028, hlam]
          · rcases p24013_3 (m.d 0 2) (by simp) with h24030 | h24030
            · rcases p24013_3 (m.d 0 3) (by simp) with h24031 | h24031
              · linarith only [h20408, h24031, hlam]
              · linarith only [h20411, h24031, hlam]
            · linarith only [h20409, h24030, hlam]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          rcases p24013_3 (m.d 0 1) (by simp) with h24035 | h24035
          · linarith only [h0, h24035, hlam]
          · rcases p24013_3 (m.d 0 2) (by simp) with h24037 | h24037
            · rcases p24013_3 (m.d 0 3) (by simp) with h24038 | h24038
              · linarith only [h20408, h24038, hlam]
              · linarith only [h20412, h24038, hlam]
            · linarith only [h20410, h24037, hlam]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          rcases p24013_3 (m.d 0 1) (by simp) with h24042 | h24042
          · linarith only [h14396, h24042, hlam]
          · rcases p24013_3 (m.d 0 2) (by simp) with h24044 | h24044
            · rcases p24013_3 (m.d 0 3) (by simp) with h24045 | h24045
              · rcases p24013_3 (m.d 0 4) (by simp) with h24046 | h24046
                · linarith only [h20411, h24046, hlam]
                · linarith only [h16915, h24046, hlam]
              · linarith only [h14396, h24045, hlam]
            · linarith only [h0, h24044, hlam]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h20408, hlam, p24013_1]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [hlam, p24013_0]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          rcases p24013_3 (m.d 0 1) (by simp) with h24053 | h24053
          · linarith only [h14396, h24053, hlam]
          · rcases p24013_3 (m.d 0 2) (by simp) with h24055 | h24055
            · rcases p24013_3 (m.d 0 3) (by simp) with h24056 | h24056
              · rcases p24013_3 (m.d 0 4) (by simp) with h24057 | h24057
                · linarith only [h20411, h24057, hlam]
                · rcases p24013_3 (m.d 0 5) (by simp) with h24059 | h24059
                  · linarith only [h20412, h24059, hlam]
                  · linarith only [h20413, h24059, hlam]
              · linarith only [h20411, h24056, hlam]
            · linarith only [h20409, h24055, hlam]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          rcases p24013_3 (m.d 0 1) (by simp) with h24064 | h24064
          · linarith only [h14396, h24064, hlam]
          · rcases p24013_3 (m.d 0 2) (by simp) with h24066 | h24066
            · rcases p24013_3 (m.d 0 3) (by simp) with h24067 | h24067
              · rcases p24013_3 (m.d 0 4) (by simp) with h24068 | h24068
                · linarith only [h20411, h24068, hlam]
                · rcases p24013_3 (m.d 0 5) (by simp) with h24070 | h24070
                  · linarith only [h20412, h24070, hlam]
                  · rcases h2bigk with h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c | h24072c
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h0, hlam, p24072_1]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h20408, h20411, h20413, h23282, hlam, p24013_1, p24072_2]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      rcases p24072_3 (m.d 0 2) (by simp) with h24076 | h24076
                      · rcases p24072_3 (m.d 1 2) (by simp) with h24077 | h24077
                        · rcases p24072_3 (m.d 2 3) (by simp) with h24078 | h24078
                          · linarith only [h20408, h24078, hlam]
                          · rcases p24072_3 (m.d 2 4) (by simp) with h24080 | h24080
                            · linarith only [h24080, hlam, p24072_0]
                            · rcases p24072_3 (m.d 2 5) (by simp) with h24082 | h24082
                              · linarith only [h20410, h24082, hlam]
                              · linarith only [h24009, h24082, hlam]
                        · linarith only [h22730, h24077, hlam]
                      · linarith only [h24076, hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      rcases p24072_3 (m.d 0 2) (by simp) with h24087 | h24087
                      · rcases p24072_3 (m.d 1 2) (by simp) with h24088 | h24088
                        · rcases p24072_3 (m.d 2 3) (by simp) with h24089 | h24089
                          · linarith only [h20408, h24089, hlam]
                          · rcases p24072_3 (m.d 2 4) (by simp) with h24091 | h24091
                            · linarith only [h20409, h24091, hlam]
                            · rcases p24072_3 (m.d 2 5) (by simp) with h24093 | h24093
                              · linarith only [h24093, hlam, p24072_0]
                              · rcases h3bigk with h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c | h24095c
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h14396, hlam, p24095_1]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  rcases p24095_3 (m.d 0 3) (by simp) with h24098 | h24098
                                  · rcases p24095_3 (m.d 1 3) (by simp) with h24099 | h24099
                                    · rcases p24095_3 (m.d 2 3) (by simp) with h24100 | h24100
                                      · linarith only [h20408, h24100, hlam]
                                      · rcases p24095_3 (m.d 3 4) (by simp) with h24102 | h24102
                                        · linarith only [h20411, h24102, hlam]
                                        · linarith only [h23282, h24102, hlam]
                                    · linarith only [h22729, h24099, hlam]
                                  · linarith only [h20408, h24098, hlam]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h20408, h23282, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24095_1]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h20408, h24005, hlam, p24072_2, p24095_1]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h14396, hc01, hc13, hlam, hphi, p24095_1]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  rcases p24095_3 (m.d 0 3) (by simp) with h24111 | h24111
                                  · linarith only [h14396, h24111, hlam]
                                  · linarith only [h20408, h24111, hlam]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h22729, h23282, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24095_1]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h22729, h23282, h24011, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24095_1]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h20408, hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h22729, hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h23282, hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h24005, hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h20411, hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h22732, hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h20408, h20411, h20413, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24013_1, p24095_1]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h24011, hlam, p24095_1]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h20412, hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h22733, hlam, p24095_0]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, p24095_1]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [h0, h20408, h20412, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24013_1, p24095_1]
                                · have p24095_0 := h24095c.1
                                  have p24095_1 := h24095c.2.1
                                  have p24095_2 := h24095c.2.2.1
                                  have p24095_3 := h24095c.2.2.2
                                  linarith only [hlam, p24095_0]
                        · linarith only [h22731, h24088, hlam]
                      · linarith only [h24087, hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h20408, h20413, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p24013_1, p24072_1]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h0, h20408, h20411, h20413, h23282, hlam, p24013_1, p24072_2]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      rcases p24072_3 (m.d 0 2) (by simp) with h24136 | h24136
                      · linarith only [h0, h24136, hlam]
                      · linarith only [h20409, h24136, hlam]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      rcases p24072_3 (m.d 0 2) (by simp) with h24139 | h24139
                      · linarith only [h0, h24139, hlam]
                      · linarith only [h20410, h24139, hlam]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h20408, hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h22729, hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h23282, hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h24005, hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h20409, hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h22730, hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h20408, h20409, h20413, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24013_1, p24072_1]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h24009, hlam, p24072_1]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h20410, hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h22731, hlam, p24072_0]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h0, h20408, h20410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24013_1, p24072_1]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [h0, h20408, h20412, h24005, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p24013_1, p24072_1]
                    · have p24072_0 := h24072c.1
                      have p24072_1 := h24072c.2.1
                      have p24072_2 := h24072c.2.2.1
                      have p24072_3 := h24072c.2.2.2
                      linarith only [hlam, p24072_0]
              · linarith only [h20412, h24067, hlam]
            · linarith only [h20410, h24066, hlam]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h16915, h22734, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p24013_1]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h20409, hlam, p24013_0]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h20411, hlam, p24013_0]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [hlam, p24013_0]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h20413, hlam, p24013_0]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          rcases p24013_3 (m.d 0 1) (by simp) with h24164 | h24164
          · linarith only [h18815, h24164, hlam]
          · rcases p24013_3 (m.d 0 2) (by simp) with h24166 | h24166
            · rcases p24013_3 (m.d 0 3) (by simp) with h24167 | h24167
              · rcases p24013_3 (m.d 0 4) (by simp) with h24168 | h24168
                · linarith only [h20413, h24168, hlam]
                · linarith only [h16915, h24168, hlam]
              · linarith only [h14396, h24167, hlam]
            · linarith only [h0, h24166, hlam]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h20410, hlam, p24013_1]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h20412, hlam, p24013_0]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [h18815, h20411, h22734, h23282, hc23, hc45, hlam, hphi, ht34, p24013_1]
        · have p24013_0 := h24013c.1
          have p24013_1 := h24013c.2.1
          have p24013_2 := h24013c.2.2.1
          have p24013_3 := h24013c.2.2.2
          linarith only [hlam, p24013_0]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h22731 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h22732 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h22733 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h22734 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 2 3 4 (by decide) (by decide) with h23282 | h23282
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730 h22731 h22732 h22733 h22734 h23282
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730 h22731 h22732 h22733 h22734 h23282

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h22731 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h22732 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h22733 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 1 4 5 (by decide) (by decide) with h22734 | h22734
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730 h22731 h22732 h22733 h22734
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730 h22731 h22732 h22733 h22734

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h22731 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h22732 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h22733 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  linarith only [h0, h14396, h20408, h20412, h22733, hc01, hc12, hlam, hphi]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h22731 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h22732 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 1 3 5 (by decide) (by decide) with h22733 | h22733
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730 h22731 h22732 h22733
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730 h22731 h22732 h22733

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h22731 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h22732 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  linarith only [h14396, h20411, h22732, hlam]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h22731 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 1 3 4 (by decide) (by decide) with h22732 | h22732
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730 h22731 h22732
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730 h22731 h22732

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h22731 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  linarith only [h0, h20410, h22731, hlam]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 1 2 5 (by decide) (by decide) with h22731 | h22731
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730 h22731
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730 h22731

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h22730 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  linarith only [h0, h20409, h22730, hlam]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 1 2 4 (by decide) (by decide) with h22730 | h22730
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729 h22730

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h22729 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  linarith only [h0, h20408, h22729, hlam]

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h20413 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 1 2 3 (by decide) (by decide) with h22729 | h22729
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413 h22729

set_option maxHeartbeats 7538000 in
set_option maxHeartbeats 7538000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s23 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg20409 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg20410 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg20411 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg20412 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  have h20409 := hg20409
  have h20410 := hg20410
  have h20411 := hg20411
  have h20412 := hg20412
  rcases m.htr 0 4 5 (by decide) (by decide) with h20413 | h20413
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413
  · exact r1l7_10_12_23_L_I_L_I_H_I_s23_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 hg20408 hg20409 hg20410 hg20411 hg20412 h20413

end R2N4
