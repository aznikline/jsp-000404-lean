import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7594 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7595 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7596 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h7597 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h7599 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 2 3 4 (by decide) (by decide) with h8003 | h8003
  · linarith only [h6793, h6799, h7593, h7594, h7599, h8003, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h8005 | h8005
    · linarith only [h0, h6794, h7373, h7593, h7594, h7597, h7599, h8005, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h8007 | h8007
      · linarith only [h7595, h7599, h8007, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h8009 | h8009
        · rcases h0bigk with h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c | h8010c
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [hlam, p8010_0]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h0, hlam, p8010_1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            rcases p8010_3 (m.d 0 1) (by simp) with h8013 | h8013
            · rcases p8010_3 (m.d 0 2) (by simp) with h8014 | h8014
              · rcases p8010_3 (m.d 0 3) (by simp) with h8015 | h8015
                · linarith only [h6793, h8015, hlam]
                · rcases p8010_3 (m.d 0 4) (by simp) with h8017 | h8017
                  · linarith only [h6794, h8017, hlam]
                  · linarith only [h6799, h8017, hlam]
              · linarith only [h6796, h8014, hlam]
            · linarith only [h6793, h8013, hlam]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h0, h7593, h7597, h7599, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8010_1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h0, h7593, h7594, h7597, h7599, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8010_1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h6793, h7594, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8010_1, u0elo1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [hlam, p8010_0]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            rcases p8010_3 (m.d 0 1) (by simp) with h8026 | h8026
            · linarith only [h0, h8026, hlam]
            · linarith only [h6793, h8026, hlam]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h7593, h7594, h7597, h7599, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8010_1, u0elo1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h7593, h7594, h7597, h7599, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8010_1, u0elo1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h6793, hlam, p8010_1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h6796, hlam, p8010_1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [hlam, p8010_0]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h6799, hlam, p8010_1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h7373, hlam, p8010_1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h6794, hlam, p8010_0]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h6797, hlam, p8010_0]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            rcases p8010_3 (m.d 0 1) (by simp) with h8038 | h8038
            · rcases p8010_3 (m.d 0 2) (by simp) with h8039 | h8039
              · rcases p8010_3 (m.d 0 3) (by simp) with h8040 | h8040
                · linarith only [h6799, h8040, hlam]
                · rcases p8010_3 (m.d 0 4) (by simp) with h8042 | h8042
                  · rcases p8010_3 (m.d 0 5) (by simp) with h8043 | h8043
                    · linarith only [h7593, h8043, hlam]
                    · linarith only [h7373, h8043, hlam]
                  · linarith only [h6799, h8042, hlam]
              · linarith only [h6796, h8039, hlam]
            · linarith only [h6793, h8038, hlam]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [hlam, p8010_0]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h6794, h7593, h7594, h7597, h7599, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8010_1, u0elo0]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h6795, hlam, p8010_0]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h6798, hlam, p8010_1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            rcases p8010_3 (m.d 0 1) (by simp) with h8053 | h8053
            · rcases p8010_3 (m.d 0 2) (by simp) with h8054 | h8054
              · rcases p8010_3 (m.d 0 3) (by simp) with h8055 | h8055
                · linarith only [h7373, h8055, hlam]
                · rcases p8010_3 (m.d 0 4) (by simp) with h8057 | h8057
                  · rcases p8010_3 (m.d 0 5) (by simp) with h8058 | h8058
                    · rcases h0emin with h8059 | h8059 | h8059 | h8059 | h8059
                      · rcases h2bigk with h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h0, hlam, p8060_1]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          rcases p8060_3 (m.d 0 2) (by simp) with h8063 | h8063
                          · rcases p8060_3 (m.d 1 2) (by simp) with h8064 | h8064
                            · rcases p8060_3 (m.d 2 3) (by simp) with h8065 | h8065
                              · linarith only [h8065, hlam, p8060_0]
                              · rcases p8060_3 (m.d 2 4) (by simp) with h8067 | h8067
                                · linarith only [h6797, h8067, hlam]
                                · linarith only [h8003, h8067, hlam]
                            · linarith only [h7594, h8064, hlam]
                          · linarith only [h8063, hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          rcases p8060_3 (m.d 0 2) (by simp) with h8072 | h8072
                          · rcases p8060_3 (m.d 1 2) (by simp) with h8073 | h8073
                            · rcases p8060_3 (m.d 2 3) (by simp) with h8074 | h8074
                              · linarith only [h6796, h8074, hlam]
                              · rcases p8060_3 (m.d 2 4) (by simp) with h8076 | h8076
                                · linarith only [h8076, hlam, p8060_0]
                                · rcases p8060_3 (m.d 2 5) (by simp) with h8078 | h8078
                                  · linarith only [h6798, h8078, hlam]
                                  · linarith only [h8007, h8078, hlam]
                            · linarith only [h7595, h8073, hlam]
                          · linarith only [h8072, hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          rcases p8060_3 (m.d 0 2) (by simp) with h8083 | h8083
                          · rcases p8060_3 (m.d 1 2) (by simp) with h8084 | h8084
                            · rcases p8060_3 (m.d 2 3) (by simp) with h8085 | h8085
                              · linarith only [h6796, h8085, hlam]
                              · rcases p8060_3 (m.d 2 4) (by simp) with h8087 | h8087
                                · linarith only [h6797, h8087, hlam]
                                · rcases p8060_3 (m.d 2 5) (by simp) with h8089 | h8089
                                  · linarith only [h8089, hlam, p8060_0]
                                  · rcases h4bigk with h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c | h8091c
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [hlam, p8091_0]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      rcases p8091_3 (m.d 0 4) (by simp) with h8093 | h8093
                                      · rcases p8091_3 (m.d 1 4) (by simp) with h8094 | h8094
                                        · linarith only [h6794, h8094, hlam]
                                        · rcases p8091_3 (m.d 2 4) (by simp) with h8096 | h8096
                                          · linarith only [h6797, h8096, hlam]
                                          · rcases p8091_3 (m.d 3 4) (by simp) with h8098 | h8098
                                            · rcases p8091_3 (m.d 4 5) (by simp) with h8099 | h8099
                                              · linarith only [h7593, h8099, hlam]
                                              · linarith only [h7599, h8099, hlam]
                                            · linarith only [h7597, h8098, hlam]
                                      · linarith only [h6794, h8093, hlam]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      rcases p8091_3 (m.d 0 4) (by simp) with h8104 | h8104
                                      · rcases p8091_3 (m.d 1 4) (by simp) with h8105 | h8105
                                        · linarith only [h6794, h8105, hlam]
                                        · linarith only [h7595, h8105, hlam]
                                      · linarith only [h6797, h8104, hlam]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h6799, hlam, p8091_0]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h0, h6794, h7594, h7597, h7599, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8091_1]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h6794, hlam, p8091_1]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [hlam, p8091_0]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h7599, h8003, hc23, hc45, hlam, hphi, ht34, p8091_1]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h7597, hlam, p8091_1]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h7599, hlam, p8091_0]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h6797, hlam, p8091_1]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h7595, hlam, p8091_1]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [hlam, p8091_0]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h8003, hlam, p8091_1]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h8007, hlam, p8091_0]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h6793, h7593, h7594, hc23, hc34, hlam, hphi, p8010_1, p8091_1]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      rcases p8091_3 (m.d 0 4) (by simp) with h8122 | h8122
                                      · linarith only [h6799, h8122, hlam]
                                      · linarith only [h6794, h8122, hlam]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      rcases p8091_3 (m.d 0 4) (by simp) with h8125 | h8125
                                      · linarith only [h6799, h8125, hlam]
                                      · linarith only [h6797, h8125, hlam]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [hlam, p8091_0]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h7595, h7599, h8003, hc23, hc34, hlam, hphi, p8091_1]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h7593, hlam, p8091_0]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h7593, hc14, hlam, hphi, ht0b, ht45, ht5b, p8091_1, u0elo3]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h0, h6794, h7593, h8003, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8091_1]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [h8009, hlam, p8091_0]
                                    · have p8091_0 := h8091c.1
                                      have p8091_1 := h8091c.2.1
                                      have p8091_2 := h8091c.2.2.1
                                      have p8091_3 := h8091c.2.2.2
                                      linarith only [hlam, p8091_0]
                            · linarith only [h7596, h8084, hlam]
                          · linarith only [h8083, hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h0, h8059, hc12, hlam, ht01, p8060_1]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h0, h6793, h6794, h7593, h7594, hlam, p8010_1, p8060_2]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h0, h6794, h7593, h7595, h7599, hlam, p8060_2]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          rcases p8060_3 (m.d 0 2) (by simp) with h8141 | h8141
                          · linarith only [h0, h8141, hlam]
                          · linarith only [h6798, h8141, hlam]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h6796, hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h7594, hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h8003, hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h8005, hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h6797, hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h7595, hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h6794, h7593, h7595, h7599, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8060_1, u0elo0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h8007, hlam, p8060_1]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h6798, hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h7596, hlam, p8060_0]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8060_1, u0elo1]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [h0, h6794, h7593, h7596, h7599, hc24, hlam, hphi, ht0b, ht45, ht5b, p8060_1, u0elo1]
                        · have p8060_0 := h8060c.1
                          have p8060_1 := h8060c.2.1
                          have p8060_2 := h8060c.2.2.1
                          have p8060_3 := h8060c.2.2.2
                          linarith only [hlam, p8060_0]
                      · rcases h2bigk with h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c | h8159c
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h0, hlam, p8159_1]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          rcases p8159_3 (m.d 0 2) (by simp) with h8162 | h8162
                          · rcases p8159_3 (m.d 1 2) (by simp) with h8163 | h8163
                            · rcases p8159_3 (m.d 2 3) (by simp) with h8164 | h8164
                              · linarith only [h8164, hlam, p8159_0]
                              · rcases p8159_3 (m.d 2 4) (by simp) with h8166 | h8166
                                · linarith only [h6797, h8166, hlam]
                                · linarith only [h8003, h8166, hlam]
                            · linarith only [h7594, h8163, hlam]
                          · linarith only [h8162, hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          rcases p8159_3 (m.d 0 2) (by simp) with h8171 | h8171
                          · rcases p8159_3 (m.d 1 2) (by simp) with h8172 | h8172
                            · rcases p8159_3 (m.d 2 3) (by simp) with h8173 | h8173
                              · linarith only [h6796, h8173, hlam]
                              · rcases p8159_3 (m.d 2 4) (by simp) with h8175 | h8175
                                · linarith only [h8175, hlam, p8159_0]
                                · rcases p8159_3 (m.d 2 5) (by simp) with h8177 | h8177
                                  · linarith only [h6798, h8177, hlam]
                                  · linarith only [h8007, h8177, hlam]
                            · linarith only [h7595, h8172, hlam]
                          · linarith only [h8171, hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          rcases p8159_3 (m.d 0 2) (by simp) with h8182 | h8182
                          · rcases p8159_3 (m.d 1 2) (by simp) with h8183 | h8183
                            · rcases p8159_3 (m.d 2 3) (by simp) with h8184 | h8184
                              · linarith only [h6796, h8184, hlam]
                              · rcases p8159_3 (m.d 2 4) (by simp) with h8186 | h8186
                                · linarith only [h6797, h8186, hlam]
                                · rcases p8159_3 (m.d 2 5) (by simp) with h8188 | h8188
                                  · linarith only [h8188, hlam, p8159_0]
                                  · rcases h4bigk with h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c | h8190c
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [hlam, p8190_0]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      rcases p8190_3 (m.d 0 4) (by simp) with h8192 | h8192
                                      · rcases p8190_3 (m.d 1 4) (by simp) with h8193 | h8193
                                        · linarith only [h6794, h8193, hlam]
                                        · rcases p8190_3 (m.d 2 4) (by simp) with h8195 | h8195
                                          · linarith only [h6797, h8195, hlam]
                                          · rcases p8190_3 (m.d 3 4) (by simp) with h8197 | h8197
                                            · rcases p8190_3 (m.d 4 5) (by simp) with h8198 | h8198
                                              · linarith only [h7593, h8198, hlam]
                                              · linarith only [h7599, h8198, hlam]
                                            · linarith only [h7597, h8197, hlam]
                                      · linarith only [h6794, h8192, hlam]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      rcases p8190_3 (m.d 0 4) (by simp) with h8203 | h8203
                                      · rcases p8190_3 (m.d 1 4) (by simp) with h8204 | h8204
                                        · linarith only [h6794, h8204, hlam]
                                        · linarith only [h7595, h8204, hlam]
                                      · linarith only [h6797, h8203, hlam]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h6799, hlam, p8190_0]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h0, h6794, h7599, hc14, hlam, hphi, ht0b, ht45, ht5b, p8190_1, u0elo1]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h6794, hlam, p8190_1]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [hlam, p8190_0]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h7599, h8003, hc23, hc45, hlam, hphi, ht34, p8190_1]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h7597, hlam, p8190_1]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h7599, hlam, p8190_0]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h6797, hlam, p8190_1]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h7595, hlam, p8190_1]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [hlam, p8190_0]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h8003, hlam, p8190_1]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h8007, hlam, p8190_0]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h6793, h7593, h7594, hc23, hc34, hlam, hphi, p8010_1, p8190_1]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      rcases p8190_3 (m.d 0 4) (by simp) with h8221 | h8221
                                      · linarith only [h6799, h8221, hlam]
                                      · linarith only [h6794, h8221, hlam]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      rcases p8190_3 (m.d 0 4) (by simp) with h8224 | h8224
                                      · linarith only [h6799, h8224, hlam]
                                      · linarith only [h6797, h8224, hlam]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [hlam, p8190_0]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h7595, h7599, h8003, hc23, hc34, hlam, hphi, p8190_1]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h7593, hlam, p8190_0]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h7593, hc14, hlam, hphi, ht0b, ht45, ht5b, p8190_1, u0elo3]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h0, h6794, h7593, h8003, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8190_1, u0elo1]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [h8009, hlam, p8190_0]
                                    · have p8190_0 := h8190c.1
                                      have p8190_1 := h8190c.2.1
                                      have p8190_2 := h8190c.2.2.1
                                      have p8190_3 := h8190c.2.2.2
                                      linarith only [hlam, p8190_0]
                            · linarith only [h7596, h8183, hlam]
                          · linarith only [h8182, hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h8059, hc12, hlam, ht01, p8159_1]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h0, h6793, h6794, h7593, h7594, hlam, p8010_1, p8159_2]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h0, h6794, h7593, h7595, h7599, hlam, p8159_2]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          rcases p8159_3 (m.d 0 2) (by simp) with h8240 | h8240
                          · linarith only [h0, h8240, hlam]
                          · linarith only [h6798, h8240, hlam]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h6796, hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h7594, hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h8003, hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h8005, hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h6797, hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h7595, hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h6794, h7593, h7595, h7599, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8159_1, u0elo0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h8007, hlam, p8159_1]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h6798, hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h7596, hlam, p8159_0]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8159_1, u0elo1]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [h0, h6794, h7593, h7596, h7599, hc24, hlam, hphi, ht0b, ht45, ht5b, p8159_1, u0elo1]
                        · have p8159_0 := h8159c.1
                          have p8159_1 := h8159c.2.1
                          have p8159_2 := h8159c.2.2.1
                          have p8159_3 := h8159c.2.2.2
                          linarith only [hlam, p8159_0]
                      · linarith only [h8059, hlam, p8010_1, u0elo4]
                      · rcases h2bigk with h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c | h8259c
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h0, hlam, p8259_1]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          rcases p8259_3 (m.d 0 2) (by simp) with h8262 | h8262
                          · rcases p8259_3 (m.d 1 2) (by simp) with h8263 | h8263
                            · rcases p8259_3 (m.d 2 3) (by simp) with h8264 | h8264
                              · linarith only [h8264, hlam, p8259_0]
                              · rcases p8259_3 (m.d 2 4) (by simp) with h8266 | h8266
                                · linarith only [h6797, h8266, hlam]
                                · linarith only [h8003, h8266, hlam]
                            · linarith only [h7594, h8263, hlam]
                          · linarith only [h8262, hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          rcases p8259_3 (m.d 0 2) (by simp) with h8271 | h8271
                          · rcases p8259_3 (m.d 1 2) (by simp) with h8272 | h8272
                            · rcases p8259_3 (m.d 2 3) (by simp) with h8273 | h8273
                              · linarith only [h6796, h8273, hlam]
                              · rcases p8259_3 (m.d 2 4) (by simp) with h8275 | h8275
                                · linarith only [h8275, hlam, p8259_0]
                                · rcases p8259_3 (m.d 2 5) (by simp) with h8277 | h8277
                                  · linarith only [h6798, h8277, hlam]
                                  · linarith only [h8007, h8277, hlam]
                            · linarith only [h7595, h8272, hlam]
                          · linarith only [h8271, hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          rcases p8259_3 (m.d 0 2) (by simp) with h8282 | h8282
                          · rcases p8259_3 (m.d 1 2) (by simp) with h8283 | h8283
                            · rcases p8259_3 (m.d 2 3) (by simp) with h8284 | h8284
                              · linarith only [h6796, h8284, hlam]
                              · rcases p8259_3 (m.d 2 4) (by simp) with h8286 | h8286
                                · linarith only [h6797, h8286, hlam]
                                · rcases p8259_3 (m.d 2 5) (by simp) with h8288 | h8288
                                  · linarith only [h8288, hlam, p8259_0]
                                  · rcases h4bigk with h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c | h8290c
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [hlam, p8290_0]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      rcases p8290_3 (m.d 0 4) (by simp) with h8292 | h8292
                                      · rcases p8290_3 (m.d 1 4) (by simp) with h8293 | h8293
                                        · linarith only [h6794, h8293, hlam]
                                        · rcases p8290_3 (m.d 2 4) (by simp) with h8295 | h8295
                                          · linarith only [h6797, h8295, hlam]
                                          · rcases p8290_3 (m.d 3 4) (by simp) with h8297 | h8297
                                            · rcases p8290_3 (m.d 4 5) (by simp) with h8298 | h8298
                                              · linarith only [h7593, h8298, hlam]
                                              · linarith only [h7599, h8298, hlam]
                                            · linarith only [h7597, h8297, hlam]
                                      · linarith only [h6794, h8292, hlam]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      rcases p8290_3 (m.d 0 4) (by simp) with h8303 | h8303
                                      · rcases p8290_3 (m.d 1 4) (by simp) with h8304 | h8304
                                        · linarith only [h6794, h8304, hlam]
                                        · linarith only [h7595, h8304, hlam]
                                      · linarith only [h6797, h8303, hlam]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h6799, hlam, p8290_0]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h0, h6794, h7599, hc14, hlam, hphi, ht0b, ht45, ht5b, p8290_1, u0elo1]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h6794, hlam, p8290_1]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [hlam, p8290_0]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h7599, h8003, hc23, hc45, hlam, hphi, ht34, p8290_1]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h7597, hlam, p8290_1]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h7599, hlam, p8290_0]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h6797, hlam, p8290_1]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h7595, hlam, p8290_1]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [hlam, p8290_0]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h8003, hlam, p8290_1]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h8007, hlam, p8290_0]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h7593, hc03, hc34, hlam, hphi, p8010_1, p8290_1]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      rcases p8290_3 (m.d 0 4) (by simp) with h8321 | h8321
                                      · linarith only [h6799, h8321, hlam]
                                      · linarith only [h6794, h8321, hlam]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      rcases p8290_3 (m.d 0 4) (by simp) with h8324 | h8324
                                      · linarith only [h6799, h8324, hlam]
                                      · linarith only [h6797, h8324, hlam]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [hlam, p8290_0]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h7595, h7599, h8003, hc23, hc34, hlam, hphi, p8290_1]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h7593, hlam, p8290_0]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h0, h6794, h7593, hc14, hlam, hphi, ht0b, ht45, ht5b, p8290_1, u0elo1]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h0, h6794, h7593, h8003, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8290_1, u0elo1]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [h8009, hlam, p8290_0]
                                    · have p8290_0 := h8290c.1
                                      have p8290_1 := h8290c.2.1
                                      have p8290_2 := h8290c.2.2.1
                                      have p8290_3 := h8290c.2.2.2
                                      linarith only [hlam, p8290_0]
                            · linarith only [h7596, h8283, hlam]
                          · linarith only [h8282, hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h0, h6794, h8059, hc12, hlam, ht01, p8259_1]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h0, h6793, h6794, h7593, h7594, hlam, p8010_1, p8259_2]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h0, h6794, h7593, h7595, h7599, hlam, p8259_2]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          rcases p8259_3 (m.d 0 2) (by simp) with h8340 | h8340
                          · linarith only [h0, h8340, hlam]
                          · linarith only [h6798, h8340, hlam]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h6796, hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h7594, hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h8003, hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h8005, hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h6797, hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h7595, hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h6794, h7593, h7595, h7599, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8259_1, u0elo0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h8007, hlam, p8259_1]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h6798, hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h7596, hlam, p8259_0]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8259_1, u0elo1]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [h0, h6794, h7593, h7596, h7599, hc24, hlam, hphi, ht0b, ht45, ht5b, p8259_1, u0elo1]
                        · have p8259_0 := h8259c.1
                          have p8259_1 := h8259c.2.1
                          have p8259_2 := h8259c.2.2.1
                          have p8259_3 := h8259c.2.2.2
                          linarith only [hlam, p8259_0]
                      · rcases h2bigk with h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c | h8358c
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h0, hlam, p8358_1]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          rcases p8358_3 (m.d 0 2) (by simp) with h8361 | h8361
                          · rcases p8358_3 (m.d 1 2) (by simp) with h8362 | h8362
                            · rcases p8358_3 (m.d 2 3) (by simp) with h8363 | h8363
                              · linarith only [h8363, hlam, p8358_0]
                              · rcases p8358_3 (m.d 2 4) (by simp) with h8365 | h8365
                                · linarith only [h6797, h8365, hlam]
                                · linarith only [h8003, h8365, hlam]
                            · linarith only [h7594, h8362, hlam]
                          · linarith only [h8361, hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          rcases p8358_3 (m.d 0 2) (by simp) with h8370 | h8370
                          · rcases p8358_3 (m.d 1 2) (by simp) with h8371 | h8371
                            · rcases p8358_3 (m.d 2 3) (by simp) with h8372 | h8372
                              · linarith only [h6796, h8372, hlam]
                              · rcases p8358_3 (m.d 2 4) (by simp) with h8374 | h8374
                                · linarith only [h8374, hlam, p8358_0]
                                · rcases p8358_3 (m.d 2 5) (by simp) with h8376 | h8376
                                  · linarith only [h6798, h8376, hlam]
                                  · linarith only [h8007, h8376, hlam]
                            · linarith only [h7595, h8371, hlam]
                          · linarith only [h8370, hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          rcases p8358_3 (m.d 0 2) (by simp) with h8381 | h8381
                          · rcases p8358_3 (m.d 1 2) (by simp) with h8382 | h8382
                            · rcases p8358_3 (m.d 2 3) (by simp) with h8383 | h8383
                              · linarith only [h6796, h8383, hlam]
                              · rcases p8358_3 (m.d 2 4) (by simp) with h8385 | h8385
                                · linarith only [h6797, h8385, hlam]
                                · rcases p8358_3 (m.d 2 5) (by simp) with h8387 | h8387
                                  · linarith only [h8387, hlam, p8358_0]
                                  · rcases h4bigk with h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c | h8389c
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [hlam, p8389_0]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      rcases p8389_3 (m.d 0 4) (by simp) with h8391 | h8391
                                      · rcases p8389_3 (m.d 1 4) (by simp) with h8392 | h8392
                                        · linarith only [h6794, h8392, hlam]
                                        · rcases p8389_3 (m.d 2 4) (by simp) with h8394 | h8394
                                          · linarith only [h6797, h8394, hlam]
                                          · rcases p8389_3 (m.d 3 4) (by simp) with h8396 | h8396
                                            · rcases p8389_3 (m.d 4 5) (by simp) with h8397 | h8397
                                              · linarith only [h7593, h8397, hlam]
                                              · linarith only [h7599, h8397, hlam]
                                            · linarith only [h7597, h8396, hlam]
                                      · linarith only [h6794, h8391, hlam]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      rcases p8389_3 (m.d 0 4) (by simp) with h8402 | h8402
                                      · rcases p8389_3 (m.d 1 4) (by simp) with h8403 | h8403
                                        · linarith only [h6794, h8403, hlam]
                                        · linarith only [h7595, h8403, hlam]
                                      · linarith only [h6797, h8402, hlam]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h6799, hlam, p8389_0]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h0, h6794, h7599, hc14, hlam, hphi, ht0b, ht45, ht5b, p8389_1, u0elo1]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h6794, hlam, p8389_1]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [hlam, p8389_0]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h7599, h8003, hc23, hc45, hlam, hphi, ht34, p8389_1]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h7597, hlam, p8389_1]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h7599, hlam, p8389_0]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h6797, hlam, p8389_1]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h7595, hlam, p8389_1]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [hlam, p8389_0]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h8003, hlam, p8389_1]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h8007, hlam, p8389_0]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h6793, h7593, h7594, hc23, hc34, hlam, hphi, p8010_1, p8389_1]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      rcases p8389_3 (m.d 0 4) (by simp) with h8420 | h8420
                                      · linarith only [h6799, h8420, hlam]
                                      · linarith only [h6794, h8420, hlam]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      rcases p8389_3 (m.d 0 4) (by simp) with h8423 | h8423
                                      · linarith only [h6799, h8423, hlam]
                                      · linarith only [h6797, h8423, hlam]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [hlam, p8389_0]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h7595, h7599, h8003, hc23, hc34, hlam, hphi, p8389_1]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h7593, hlam, p8389_0]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h7593, hc14, hlam, hphi, ht0b, ht45, ht5b, p8389_1, u0elo3]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h0, h6794, h7593, h8003, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8389_1, u0elo1]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [h8009, hlam, p8389_0]
                                    · have p8389_0 := h8389c.1
                                      have p8389_1 := h8389c.2.1
                                      have p8389_2 := h8389c.2.2.1
                                      have p8389_3 := h8389c.2.2.2
                                      linarith only [hlam, p8389_0]
                            · linarith only [h7596, h8382, hlam]
                          · linarith only [h8381, hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h0, h6793, h6795, h7594, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8010_1, p8358_1]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h0, h6793, h6794, h7593, h7594, hlam, p8010_1, p8358_2]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h0, h6794, h7593, h7595, h7599, hlam, p8358_2]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          rcases p8358_3 (m.d 0 2) (by simp) with h8439 | h8439
                          · linarith only [h0, h8439, hlam]
                          · linarith only [h6798, h8439, hlam]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h6796, hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h7594, hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h8003, hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h8005, hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h6797, hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h7595, hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h6794, h7593, h7595, h7599, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8358_1, u0elo0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h8007, hlam, p8358_1]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h6798, hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h7596, hlam, p8358_0]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h6798, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8358_1, u0elo1]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [h0, h6794, h7593, h7596, h7599, hc24, hlam, hphi, ht0b, ht45, ht5b, p8358_1, u0elo1]
                        · have p8358_0 := h8358c.1
                          have p8358_1 := h8358c.2.1
                          have p8358_2 := h8358c.2.2.1
                          have p8358_3 := h8358c.2.2.2
                          linarith only [hlam, p8358_0]
                    · linarith only [h7373, h8058, hlam]
                  · linarith only [h6799, h8057, hlam]
              · linarith only [h6796, h8054, hlam]
            · linarith only [h6793, h8053, hlam]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [h7593, hlam, p8010_1]
          · have p8010_0 := h8010c.1
            have p8010_1 := h8010c.2.1
            have p8010_2 := h8010c.2.2.1
            have p8010_3 := h8010c.2.2.2
            linarith only [hlam, p8010_0]
        · linarith only [h0, h6793, h6794, h6799, h7593, h7594, h8009, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7594 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7595 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7596 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h7597 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 1 4 5 (by decide) (by decide) with h7599 | h7599
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h7594 h7595 h7596 h7597 h7599
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h7594 h7595 h7596 h7597 h7599

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7594 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7595 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7596 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 1 3 4 (by decide) (by decide) with h7597 | h7597
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h7594 h7595 h7596 h7597
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h7594 h7595 h7596 h7597

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7594 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7595 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h7596 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h0, h6798, h7596, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7594 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7595 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 1 2 5 (by decide) (by decide) with h7596 | h7596
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h7594 h7595 h7596
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h7594 h7595 h7596

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7594 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h7595 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h0, h6797, h7595, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7594 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 1 2 4 (by decide) (by decide) with h7595 | h7595
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h7594 h7595
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h7594 h7595

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7594 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h0, h6796, h7594, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  rcases m.htr 1 2 3 (by decide) (by decide) with h7594 | h7594
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h7594
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg6794 h6795 h6796 h6797 h6798 h6799 h7373 h7593 h7594

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h6793, h6799, h8470, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8472 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h6794, h7593, h8472, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8472 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8474 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h6793, h6799, h8467, h8474, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8472 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8474 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8476 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h6793, h7373, h8467, h8476, hlam]

set_option maxHeartbeats 5276000 in
set_option maxHeartbeats 5276000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s9_x0_x0_x0_x0_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg6794 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6795 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h6796 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h6797 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6798 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6799 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h7373 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h7593 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h8467 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h8468 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h8469 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h8470 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h8472 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h8474 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h8476 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h8478 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h6794 := hg6794
  linarith only [h6793, h6797, h6799, h7593, h8467, h8478, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]

end R2N4
