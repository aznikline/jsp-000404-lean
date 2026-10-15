import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_66S2

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_I_L_0_L_0_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h677 | h677
  · rcases m.htr 0 3 5 (by decide) (by decide) with h678 | h678
    · rcases m.htr 0 4 5 (by decide) (by decide) with h679 | h679
      · rcases m.htr 1 2 5 (by decide) (by decide) with h680 | h680
        · rcases m.htr 1 3 4 (by decide) (by decide) with h681 | h681
          · rcases m.htr 1 3 5 (by decide) (by decide) with h682 | h682
            · rcases m.htr 1 4 5 (by decide) (by decide) with h683 | h683
              · rcases m.htr 2 3 4 (by decide) (by decide) with h684 | h684
                · rcases m.htr 2 3 5 (by decide) (by decide) with h685 | h685
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h686 | h686
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h687 | h687
                      · rcases h5bigk with h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c | h688c
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [hlam, p688_0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h0, hlam, p688_1]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h0, h680, h685, h687, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p688_1, u2elo1]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h0, h681, h683, h687, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p688_1, u3elo1]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h0, h681, h683, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p688_1, u3elo1]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h681, h683, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p688_1, u3elo1]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [hlam, p688_0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h681, h683, h685, h687, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p688_1, u3elo1]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h681, h683, h687, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p688_1, u3elo1]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h681, h683, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p688_1, u3elo1]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h677, hlam, p688_1]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h680, hlam, p688_1]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [hlam, p688_0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h677, h687, hc02, hc45, hlam, hphi, ht0b, ht5b, p688_1]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h677, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p688_1, u2elo0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h678, hlam, p688_0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h682, hlam, p688_0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h685, hlam, p688_0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [hlam, p688_0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p688_1, u3elo4]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h679, hlam, p688_0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h683, hlam, p688_0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h686, hlam, p688_0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [h687, hlam, p688_0]
                        · have p688_0 := h688c.1
                          have p688_1 := h688c.2.1
                          have p688_2 := h688c.2.2.1
                          have p688_3 := h688c.2.2.2
                          linarith only [hlam, p688_0]
                      · rcases h5bigk with h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c | h714c
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h0, hlam, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h0, h681, h683, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p714_1, u3elo1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h0, h681, h683, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p714_1, u3elo1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h0, h681, h683, h687, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p714_1, u3elo1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h681, h683, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p714_1, u3elo1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h681, h683, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p714_1, u3elo1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h681, h683, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p714_1, u3elo1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h681, h683, h687, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p714_1, u3elo1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h677, hlam, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h680, hlam, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p714_1, u2elo4]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h677, h687, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h678, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h682, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h685, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h687, hlam, p714_1]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h679, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h683, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h686, hlam, p714_0]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [h684, h686, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p714_1, u2elo2]
                        · have p714_0 := h714c.1
                          have p714_1 := h714c.2.1
                          have p714_2 := h714c.2.2.1
                          have p714_3 := h714c.2.2.2
                          linarith only [hlam, p714_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h740 | h740
                      · linarith only [h681, h686, h740, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · rcases h5bigk with h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c | h742c
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [hlam, p742_0]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h0, hlam, p742_1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h0, h681, h683, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p742_1, u3elo1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h0, h681, h683, h740, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p742_1, u3elo1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h0, h681, h683, h684, h686, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p742_1, u3elo1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h681, h683, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p742_1, u3elo1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [hlam, p742_0]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h681, h683, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p742_1, u3elo1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h681, h683, h740, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p742_1, u3elo1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h681, h683, h684, h686, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p742_1, u3elo1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h677, hlam, p742_1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h680, hlam, p742_1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [hlam, p742_0]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h740, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p742_1, u2elo4]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h686, hlam, p742_1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h678, hlam, p742_0]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h682, hlam, p742_0]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h685, hlam, p742_0]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [hlam, p742_0]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h740, hlam, p742_1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h679, hlam, p742_0]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h683, hlam, p742_0]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h679, hc04, hc25, hlam, hphi, ht0b, ht5b, p742_1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [h740, hc34, hc45, hlam, hphi, p742_1]
                        · have p742_0 := h742c.1
                          have p742_1 := h742c.2.1
                          have p742_2 := h742c.2.2.1
                          have p742_3 := h742c.2.2.2
                          linarith only [hlam, p742_0]
                  · linarith only [h678, h685, hc23, hlam, hphi, u3elo0]
                · linarith only [h681, h684, hc23, hlam, hphi, u3elo1]
              · linarith only [h0, h679, h683, hlam]
            · linarith only [h678, h682, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h772 | h772
            · linarith only [h0, h681, h772, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h678, h772, hc13, hlam, hphi, u3elo0]
        · linarith only [h677, h680, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h776 | h776
        · rcases m.htr 1 3 4 (by decide) (by decide) with h777 | h777
          · rcases m.htr 1 3 5 (by decide) (by decide) with h778 | h778
            · rcases m.htr 1 4 5 (by decide) (by decide) with h779 | h779
              · rcases m.htr 2 3 4 (by decide) (by decide) with h780 | h780
                · rcases m.htr 2 3 5 (by decide) (by decide) with h781 | h781
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h782 | h782
                    · linarith only [h677, h679, h782, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h784 | h784
                      · linarith only [h780, h782, h784, hlam]
                      · rcases h5bigk with h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h0, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h679, h777, h779, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h679, h777, h779, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p786_1, u3elo1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h679, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h776, h781, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p786_1, u2elo1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h778, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p786_1, u3elo1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h777, h779, h780, h782, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p786_1, u3elo1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h677, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h776, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p786_1, u2elo4]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h782, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h678, hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h778, hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h781, hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h784, hlam, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p786_1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h779, hlam, p786_0]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h777, h779, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p786_1, u3elo1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [h777, h779, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p786_1, u3elo1]
                        · have p786_0 := h786c.1
                          have p786_1 := h786c.2.1
                          have p786_2 := h786c.2.2.1
                          have p786_3 := h786c.2.2.2
                          linarith only [hlam, p786_0]
                  · linarith only [h678, h780, h781, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                · linarith only [h777, h780, hc23, hlam, hphi, u3elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h814 | h814
                · rcases m.htr 2 3 5 (by decide) (by decide) with h815 | h815
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h816 | h816
                    · linarith only [h0, h779, h816, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h818 | h818
                      · linarith only [h0, h779, h814, h818, hc01, hlam, hphi, ht12, u2elo3]
                      · rcases h5bigk with h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c | h820c
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [hlam, p820_0]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h0, hlam, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h677, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p820_1, u2elo0]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h678, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p820_1, u3elo0]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h679, hlam, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h0, h779, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [hlam, p820_0]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h776, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p820_1, u2elo1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h778, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p820_1, u3elo1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h779, hlam, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h677, hlam, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h776, hlam, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [hlam, p820_0]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p820_1, u2elo4]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h816, hlam, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h678, hlam, p820_0]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h778, hlam, p820_0]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h815, hlam, p820_0]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [hlam, p820_0]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h818, hlam, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h779, hc14, hc45, hlam, hphi, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h816, hc24, hc45, hlam, hphi, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [h818, hc34, hc45, hlam, hphi, p820_1]
                        · have p820_0 := h820c.1
                          have p820_1 := h820c.2.1
                          have p820_2 := h820c.2.2.1
                          have p820_3 := h820c.2.2.2
                          linarith only [hlam, p820_0]
                  · linarith only [h678, h815, hc23, hlam, hphi, u3elo0]
                · linarith only [h777, h814, hc23, hlam, hphi, u3elo1]
            · linarith only [h678, h777, h778, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h849 | h849
            · linarith only [h0, h777, h849, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h678, h849, hc13, hlam, hphi, u3elo0]
        · linarith only [h677, h776, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h853 | h853
      · rcases m.htr 1 2 5 (by decide) (by decide) with h854 | h854
        · rcases m.htr 1 3 4 (by decide) (by decide) with h855 | h855
          · rcases m.htr 1 3 5 (by decide) (by decide) with h856 | h856
            · linarith only [h678, h856, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h858 | h858
              · linarith only [h0, h855, h856, h858, hc01, hlam, hphi, ht12, ht23, u3elo4]
              · linarith only [h0, h853, h858, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h861 | h861
            · linarith only [h678, h855, h861, hc03, hlam, hphi, u3elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h863 | h863
              · rcases m.htr 2 3 4 (by decide) (by decide) with h864 | h864
                · linarith only [h855, h864, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h866 | h866
                  · linarith only [h0, h861, h866, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h868 | h868
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h869 | h869
                      · rcases h5bigk with h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c | h870c
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [hlam, p870_0]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h0, hlam, p870_1]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h0, h861, h866, hc23, hlam, hphi, p870_1, u3elo4]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h678, hlam, p870_1]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h0, h861, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p870_1, u3elo4]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h861, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p870_1, u3elo4]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [hlam, p870_0]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h861, h866, hc23, hlam, hphi, p870_1, u3elo4]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h861, hlam, p870_1]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h855, h863, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p870_1, u3elo3]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h677, hlam, p870_1]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h854, hlam, p870_1]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [hlam, p870_0]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h866, hlam, p870_1]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p870_1, u2elo4]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p870_1, u3elo4]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p870_1, u3elo4]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p870_1, u3elo4]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [hlam, p870_0]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h869, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p870_1, u3elo3]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h853, hlam, p870_0]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h863, hlam, p870_0]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h868, hlam, p870_0]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [h869, hlam, p870_0]
                        · have p870_0 := h870c.1
                          have p870_1 := h870c.2.1
                          have p870_2 := h870c.2.2.1
                          have p870_3 := h870c.2.2.2
                          linarith only [hlam, p870_0]
                      · linarith only [h678, h853, h855, h869, hc13, hlam, hphi, u3elo4]
                    · linarith only [h855, h863, h864, h868, hc23, hlam, hphi, u3elo3]
              · linarith only [h0, h853, h863, hlam]
        · linarith only [h677, h854, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h900 | h900
        · rcases m.htr 1 3 4 (by decide) (by decide) with h901 | h901
          · rcases m.htr 1 3 5 (by decide) (by decide) with h902 | h902
            · linarith only [h678, h902, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h904 | h904
              · linarith only [h853, h901, h902, h904, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h906 | h906
                · rcases m.htr 2 3 5 (by decide) (by decide) with h907 | h907
                  · linarith only [h902, h907, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h909 | h909
                    · linarith only [h0, h904, h909, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h911 | h911
                      · linarith only [h0, h901, h904, h911, hc01, hc13, hlam, hphi]
                      · rcases h5bigk with h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c | h913c
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [hlam, p913_0]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h0, hlam, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h677, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p913_1, u2elo0]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h678, hlam, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h853, hlam, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [hlam, p913_0]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h900, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p913_1, u2elo1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h902, hlam, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h904, hlam, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h677, hlam, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h900, hlam, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [hlam, p913_0]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h907, hlam, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h909, hlam, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, ht23, p913_1, u3elo4]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p913_1, u3elo4]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p913_1, u3elo4]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [hlam, p913_0]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h911, hlam, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h907, hc23, hc45, hlam, hphi, ht34, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [h902, hc13, hc45, hlam, hphi, ht34, p913_1]
                        · have p913_0 := h913c.1
                          have p913_1 := h913c.2.1
                          have p913_2 := h913c.2.2.1
                          have p913_3 := h913c.2.2.2
                          linarith only [hlam, p913_0]
                · linarith only [h901, h902, h906, hc23, hlam, hphi, u3elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h940 | h940
            · linarith only [h678, h901, h940, hc03, hlam, hphi, u3elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h942 | h942
              · rcases m.htr 2 3 4 (by decide) (by decide) with h943 | h943
                · linarith only [h901, h943, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h945 | h945
                  · linarith only [h0, h940, h945, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h947 | h947
                    · linarith only [h677, h853, h947, hlam]
                    · linarith only [h901, h942, h943, h947, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h950 | h950
                · linarith only [h901, h950, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h952 | h952
                  · linarith only [h0, h940, h952, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h954 | h954
                    · linarith only [h0, h942, h954, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h956 | h956
                      · linarith only [h0, h942, h956, hc01, hlam, hphi, ht12, ht23, u3elo3]
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
                          linarith only [h0, hlam, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h0, h940, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p958_1, u3elo4]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h678, hlam, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h853, hlam, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h940, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p958_1, u3elo4]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [hlam, p958_0]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h940, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p958_1, u3elo4]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h940, hlam, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h942, hlam, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h677, hlam, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h900, hlam, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [hlam, p958_0]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h952, hlam, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h954, hlam, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, ht23, p958_1, u3elo4]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p958_1, u3elo4]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p958_1, u3elo4]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [hlam, p958_0]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h956, hlam, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h952, hc23, hc45, hlam, hphi, ht34, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [h678, hc03, hc45, hlam, hphi, ht34, p958_1]
                        · have p958_0 := h958c.1
                          have p958_1 := h958c.2.1
                          have p958_2 := h958c.2.2.1
                          have p958_3 := h958c.2.2.2
                          linarith only [hlam, p958_0]
        · linarith only [h677, h900, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h985 | h985
    · rcases m.htr 0 4 5 (by decide) (by decide) with h986 | h986
      · rcases m.htr 1 2 5 (by decide) (by decide) with h987 | h987
        · linarith only [h677, h987, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h989 | h989
          · rcases m.htr 1 3 5 (by decide) (by decide) with h990 | h990
            · rcases m.htr 1 4 5 (by decide) (by decide) with h991 | h991
              · rcases m.htr 2 3 4 (by decide) (by decide) with h992 | h992
                · rcases m.htr 2 3 5 (by decide) (by decide) with h993 | h993
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h994 | h994
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h995 | h995
                      · rcases h5bigk with h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h0, hlam, p996_1]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h677, hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h0, h987, h992, h994, h995, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p996_1, u2elo2]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h0, h987, h992, h994, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p996_1, u3elo2]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h987, h992, h994, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p996_1, u3elo2]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h987, hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h987, h992, h994, h995, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p996_1, u3elo2]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h987, h992, h994, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p996_1, u3elo2]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h0, h992, h994, hc01, hlam, hphi, ht12, ht23, p996_1, u3elo2]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h992, h994, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p996_1, u3elo2]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h992, h994, h995, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p996_1, u3elo2]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h992, h994, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p996_1, u3elo2]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h985, hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h990, hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h993, hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h985, hc03, hc45, hlam, hphi, ht0b, ht5b, p996_1]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h986, hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h991, hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h994, hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [h995, hlam, p996_0]
                        · have p996_0 := h996c.1
                          have p996_1 := h996c.2.1
                          have p996_2 := h996c.2.2.1
                          have p996_3 := h996c.2.2.2
                          linarith only [hlam, p996_0]
                      · rcases h5bigk with h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h0, hlam, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h677, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h677, h992, h994, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1022_1, u3elo2]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h677, h992, h994, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1022_1, u3elo2]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h987, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h987, h992, h994, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1022_1, u3elo2]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h987, h992, h994, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1022_1, u3elo2]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h0, h992, h994, hc01, hlam, hphi, ht12, ht23, p1022_1, u3elo2]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h992, h994, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1022_1, u3elo2]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h992, h994, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1022_1, u3elo2]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h992, h994, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1022_1, u3elo2]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h985, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h990, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h993, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h995, hlam, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h986, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h991, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h994, hlam, p1022_0]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [h986, hc04, hc35, hlam, hphi, ht0b, ht5b, p1022_1]
                        · have p1022_0 := h1022c.1
                          have p1022_1 := h1022c.2.1
                          have p1022_2 := h1022c.2.2.1
                          have p1022_3 := h1022c.2.2.2
                          linarith only [hlam, p1022_0]
                    · linarith only [h677, h989, h991, h994, hc02, hlam, hphi, ht23, u3elo1]
                  · linarith only [h985, h993, hc23, hlam, hphi, u3elo0]
                · linarith only [h989, h992, hc23, hlam, hphi, u3elo1]
              · linarith only [h0, h986, h991, hlam]
            · linarith only [h985, h990, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1053 | h1053
            · linarith only [h0, h1053, h989, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h1053, h985, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1056 | h1056
        · linarith only [h1056, h677, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1058 | h1058
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1059 | h1059
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1060 | h1060
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1061 | h1061
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1062 | h1062
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1063 | h1063
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1064 | h1064
                      · linarith only [h1058, h1064, h986, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
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
                          linarith only [h0, hlam, p1066_1]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h677, hlam, p1066_0]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h0, h1056, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1066_1, u2elo4]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h986, hlam, p1066_1]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1056, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1066_1, u2elo4]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [hlam, p1066_0]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1056, hlam, p1066_0]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1059, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1, u3elo1]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1058, h1060, h986, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1066_1, u3elo1]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, p1066_1, u2elo4]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1066_1, u2elo4]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [hlam, p1066_0]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1062, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1, u3elo2]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1061, h1063, h986, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1066_1, u3elo2]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h985, hlam, p1066_0]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1059, hlam, p1066_0]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1062, hlam, p1066_0]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [hlam, p1066_0]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1064, hlam, p1066_1]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1066_1]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1060, hlam, p1066_0]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1063, hlam, p1066_0]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [h1058, h1060, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1066_1, u3elo1]
                        · have p1066_0 := h1066c.1
                          have p1066_1 := h1066c.2.1
                          have p1066_2 := h1066c.2.2.1
                          have p1066_3 := h1066c.2.2.2
                          linarith only [hlam, p1066_0]
                    · linarith only [h1056, h1058, h1060, h1063, hc12, hlam, hphi, ht23, u3elo1]
                  · linarith only [h1062, h985, hc23, hlam, hphi, u3elo0]
                · linarith only [h1058, h1061, hc23, hlam, hphi, u3elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1095 | h1095
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1096 | h1096
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1097 | h1097
                    · linarith only [h0, h1060, h1097, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1099 | h1099
                      · linarith only [h1058, h1060, h1099, hlam]
                      · rcases h5bigk with h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c | h1101c
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [hlam, p1101_0]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h0, hlam, p1101_1]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h677, hlam, p1101_0]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h0, h1056, h1096, h1099, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1101_1, u2elo2]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h986, hlam, p1101_1]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h1056, h1096, h986, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1101_1, u2elo2]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [hlam, p1101_0]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h1056, hlam, p1101_0]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h1056, h1096, h1099, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1101_1, u3elo2]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h1060, hlam, p1101_1]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h0, h1096, hc01, hlam, hphi, ht12, ht23, p1101_1, u3elo2]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h1096, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1101_1, u3elo2]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [hlam, p1101_0]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h1096, h1099, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1101_1, u3elo2]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h1097, hlam, p1101_1]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h985, hlam, p1101_0]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h1059, hlam, p1101_0]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h1096, hlam, p1101_0]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [hlam, p1101_0]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h1099, hlam, p1101_1]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1101_1]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1101_1]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h677, hc02, hc45, hlam, hphi, ht23, ht34, p1101_1]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [h1099, hc34, hc45, hlam, hphi, p1101_1]
                        · have p1101_0 := h1101c.1
                          have p1101_1 := h1101c.2.1
                          have p1101_2 := h1101c.2.2.1
                          have p1101_3 := h1101c.2.2.2
                          linarith only [hlam, p1101_0]
                  · linarith only [h1096, h985, hc23, hlam, hphi, u3elo0]
                · linarith only [h1058, h1095, hc23, hlam, hphi, u3elo1]
            · linarith only [h1058, h1059, h985, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1130 | h1130
            · linarith only [h0, h1058, h1130, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h1130, h985, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1133 | h1133
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1134 | h1134
        · linarith only [h1134, h677, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1136 | h1136
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1137 | h1137
            · linarith only [h1137, h985, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1139 | h1139
              · linarith only [h0, h1136, h1137, h1139, hc01, hlam, hphi, ht12, ht23, u3elo4]
              · linarith only [h0, h1133, h1139, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1142 | h1142
            · linarith only [h1136, h1142, h985, hc03, hlam, hphi, u3elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1144 | h1144
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1145 | h1145
                · linarith only [h1136, h1145, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1147 | h1147
                  · linarith only [h0, h1142, h1147, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1149 | h1149
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1150 | h1150
                      · rcases h5bigk with h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c | h1151c
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [hlam, p1151_0]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h0, hlam, p1151_1]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h677, hlam, p1151_0]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h985, hlam, p1151_1]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h0, h1134, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1151_1, u2elo4]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1134, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1151_1, u2elo4]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [hlam, p1151_0]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1134, hlam, p1151_0]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1142, hlam, p1151_1]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1134, h1147, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1151_1, u3elo4]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h0, h1147, hc01, hlam, hphi, ht12, ht23, p1151_1, u3elo4]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1147, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1151_1, u3elo4]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [hlam, p1151_0]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1147, hlam, p1151_1]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1145, h1149, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1151_1, u3elo3]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1151_1, u3elo4]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1151_1, u3elo4]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1134, hc12, hlam, hphi, ht23, p1151_1, u3elo4]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [hlam, p1151_0]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1150, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1151_1, u3elo3]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1133, hlam, p1151_0]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1144, hlam, p1151_0]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1149, hlam, p1151_0]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [h1150, hlam, p1151_0]
                        · have p1151_0 := h1151c.1
                          have p1151_1 := h1151c.2.1
                          have p1151_2 := h1151c.2.2.1
                          have p1151_3 := h1151c.2.2.2
                          linarith only [hlam, p1151_0]
                      · linarith only [h1133, h1136, h1150, h985, hc13, hlam, hphi, u3elo4]
                    · linarith only [h1136, h1144, h1145, h1149, hc23, hlam, hphi, u3elo3]
              · linarith only [h0, h1133, h1144, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1180 | h1180
        · linarith only [h1180, h677, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1182 | h1182
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1183 | h1183
            · linarith only [h1183, h985, hc03, hlam, hphi, u3elo1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1185 | h1185
              · linarith only [h1133, h1182, h1183, h1185, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1187 | h1187
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1188 | h1188
                  · linarith only [h1182, h1183, h1188, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1190 | h1190
                    · linarith only [h0, h1185, h1190, hc01, hlam, hphi, ht12, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1192 | h1192
                      · linarith only [h0, h1180, h1182, h1190, h1192, hc01, hc13, hlam, hphi]
                      · rcases h5bigk with h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c | h1194c
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [hlam, p1194_0]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h0, hlam, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h677, hlam, p1194_0]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h985, hlam, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h1133, hlam, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h1180, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1194_1, u2elo4]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [hlam, p1194_0]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h1180, hlam, p1194_0]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h1183, hlam, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h1185, hlam, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, p1194_1, u2elo4]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1194_1, u2elo4]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [hlam, p1194_0]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h1188, hlam, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h1190, hlam, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1194_1, u3elo4]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1194_1, u3elo4]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1194_1, u3elo4]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [hlam, p1194_0]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h1192, hlam, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h0, h1180, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [h1183, hc13, hc45, hlam, hphi, ht34, p1194_1]
                        · have p1194_0 := h1194c.1
                          have p1194_1 := h1194c.2.1
                          have p1194_2 := h1194c.2.2.1
                          have p1194_3 := h1194c.2.2.2
                          linarith only [hlam, p1194_0]
                · linarith only [h1182, h1183, h1187, hc23, hlam, hphi, u3elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1221 | h1221
            · linarith only [h1182, h1221, h985, hc03, hlam, hphi, u3elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1223 | h1223
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1224 | h1224
                · linarith only [h1133, h1182, h1223, h1224, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1226 | h1226
                  · linarith only [h1221, h1224, h1226, hc13, hlam, hphi, u3elo3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1228 | h1228
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1229 | h1229
                      · rcases h5bigk with h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [hlam, p1230_0]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h0, hlam, p1230_1]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h677, hlam, p1230_0]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h985, hlam, p1230_1]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h1133, hlam, p1230_1]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p1230_1]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [hlam, p1230_0]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h1180, hlam, p1230_0]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h1221, hlam, p1230_1]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h1133, h1221, h1229, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1230_1, u3elo3]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, p1230_1, u2elo4]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1230_1, u2elo4]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [hlam, p1230_0]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h1226, hlam, p1230_1]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h1133, h1226, h1229, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1230_1, u3elo3]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h0, h1229, hc01, hlam, hphi, ht12, ht23, p1230_1, u3elo3]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h0, h1229, hc01, hlam, hphi, ht12, ht23, p1230_1, u3elo3]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h1229, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1230_1, u3elo3]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [hlam, p1230_0]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h1133, h1229, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1230_1, u3elo3]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h0, h1223, hc01, hc14, hlam, hphi, p1230_1]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h1223, hlam, p1230_0]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h1228, hlam, p1230_0]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [h1229, hlam, p1230_0]
                        · have p1230_0 := h1230c.1
                          have p1230_1 := h1230c.2.1
                          have p1230_2 := h1230c.2.2.1
                          have p1230_3 := h1230c.2.2.2
                          linarith only [hlam, p1230_0]
                      · linarith only [h1182, h1223, h1229, hlam]
                    · linarith only [h1182, h1223, h1224, h1228, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1258 | h1258
                · linarith only [h1182, h1258, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1260 | h1260
                  · linarith only [h0, h1221, h1260, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1262 | h1262
                    · linarith only [h1182, h1223, h1258, h1262, hc13, hlam, hphi, u3elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1264 | h1264
                      · linarith only [h0, h1180, h1262, h1264, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases h5bigk with h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c | h1266c
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h0, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h677, hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h985, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1133, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h0, hc01, hc15, hlam, hphi, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1180, hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1221, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1223, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h0, h1260, hc01, hlam, hphi, ht12, ht23, p1266_1, u3elo4]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1260, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1266_1, u3elo4]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1260, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1262, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1266_1, u3elo4]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht12, ht23, p1266_1, u3elo4]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1266_1, u3elo4]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hlam, p1266_0]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h1264, hlam, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h0, h1180, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [h985, hc03, hc45, hlam, hphi, ht34, p1266_1]
                        · have p1266_0 := h1266c.1
                          have p1266_1 := h1266c.2.1
                          have p1266_2 := h1266c.2.2.1
                          have p1266_3 := h1266c.2.2.2
                          linarith only [hlam, p1266_0]

theorem r1l7_10_12_13_25_L_I_L_0_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_0_L_0_H_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_0_L_0_H_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
