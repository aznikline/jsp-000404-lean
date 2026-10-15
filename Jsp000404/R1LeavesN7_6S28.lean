import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S27

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11050000 in
set_option maxHeartbeats 11050000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s11 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  rcases m.htr 0 1 5 (by decide) (by decide) with h11024 | h11024
  · rcases m.htr 0 2 3 (by decide) (by decide) with h11025 | h11025
    · rcases m.htr 0 2 4 (by decide) (by decide) with h11026 | h11026
      · rcases m.htr 0 2 5 (by decide) (by decide) with h11027 | h11027
        · rcases m.htr 0 3 4 (by decide) (by decide) with h11028 | h11028
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11029 | h11029
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11030 | h11030
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11031 | h11031
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11032 | h11032
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11033 | h11033
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11034 | h11034
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11035 | h11035
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11036 | h11036
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11037 | h11037
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11038 | h11038
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11039 | h11039
                                · linarith only [h11025, h11036, h11039, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                · linarith only [h11025, h11036, h11038, h11039, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11042 | h11042
                                · linarith only [h11025, h11036, h11042, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                · rcases h0bigk with h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c | h11044c
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [hlam, p11044_0]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h0, hlam, p11044_1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h6793, hlam, p11044_0]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h10058, hlam, p11044_1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h10058, h11024, h11031, h11034, h11035, h11038, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p11044_1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11024, h11035, h11036, h11038, hc34, hlam, hphi, ht0b, ht45, ht5b, p11044_1, u0elo1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [hlam, p11044_0]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h10058, h11024, h11028, h11035, h11036, h11038, hc34, hlam, hphi, ht0b, ht45, ht5b, p11044_1, u0elo1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h10058, h11024, h11035, h11036, h11038, hc34, hlam, hphi, ht0b, ht45, ht5b, p11044_1, u0elo1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11024, h11035, h11036, h11038, hc34, hlam, hphi, ht0b, ht45, ht5b, p11044_1, u0elo1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11024, h11035, h11036, h11038, hc34, hlam, hphi, ht0b, ht45, ht5b, p11044_1, u0elo2]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11025, hlam, p11044_1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [hlam, p11044_0]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h10058, h11024, h11025, h11035, h11036, h11038, hc34, hlam, hphi, ht0b, ht45, ht5b, p11044_1, u0elo1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11024, h11025, h11035, h11036, h11038, hc34, hlam, hphi, ht0b, ht45, ht5b, p11044_1, u0elo1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11024, h11035, h11036, h11038, hc34, hlam, hphi, ht0b, ht45, ht5b, p11044_1, u0elo3]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11026, hlam, p11044_0]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11028, hlam, p11044_0]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [hlam, p11044_0]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11024, h11025, h11028, h11035, h11036, h11038, hc34, hlam, hphi, ht0b, ht45, ht5b, p11044_1, u0elo1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11024, hlam, p11044_0]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11027, hlam, p11044_1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11029, hlam, p11044_0]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [h11030, hlam, p11044_1]
                                  · have p11044_0 := h11044c.1
                                    have p11044_1 := h11044c.2.1
                                    have p11044_2 := h11044c.2.2.1
                                    have p11044_3 := h11044c.2.2.2
                                    linarith only [hlam, p11044_0]
                            · linarith only [h11025, h11029, h11036, h11037, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11071 | h11071
                            · linarith only [h11025, h11028, h11036, h11071, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11073 | h11073
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11074 | h11074
                                · rcases h0bigk with h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c | h11075c
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [hlam, p11075_0]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h0, hlam, p11075_1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h6793, hlam, p11075_0]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h10058, hlam, p11075_1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h10058, h11029, h11031, h11034, h11071, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11075_1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11024, hc15, hlam, hphi, ht0b, ht5b, p11075_1, u0elo1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [hlam, p11075_0]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11028, hc34, hlam, hphi, ht0b, ht45, ht5b, p11075_1, u0elo1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h10058, h11024, h11029, h11071, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11075_1, u0elo1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11029, h11071, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11075_1, u0elo1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11024, h11029, h11071, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11075_1, u0elo2]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11025, hlam, p11075_1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [hlam, p11075_0]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h10058, h11024, h11025, h11029, h11071, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11075_1, u0elo1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11025, h11029, h11071, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11075_1, u0elo1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11024, h11029, h11071, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11075_1, u0elo3]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11026, hlam, p11075_0]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11028, hlam, p11075_0]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [hlam, p11075_0]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11025, h11028, h11029, h11071, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11075_1, u0elo1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11024, hlam, p11075_0]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11027, hlam, p11075_1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11029, hlam, p11075_0]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [h11030, hlam, p11075_1]
                                  · have p11075_0 := h11075c.1
                                    have p11075_1 := h11075c.2.1
                                    have p11075_2 := h11075c.2.2.1
                                    have p11075_3 := h11075c.2.2.2
                                    linarith only [hlam, p11075_0]
                                · linarith only [h11026, h11036, h11073, h11074, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11102 | h11102
                                · linarith only [h11025, h11028, h11036, h11073, h11102, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                · linarith only [h11024, h11035, h11036, h11102, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h10058, h11024, h11030, h11035, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                      · linarith only [h11028, h11034, h6793, hlam]
                    · linarith only [h0, h11027, h11033, hlam]
                  · linarith only [h0, h11026, h11032, hlam]
                · linarith only [h0, h11025, h11031, hlam]
              · linarith only [h10058, h11024, h11030, hlam]
            · linarith only [h10058, h11024, h11028, h11029, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11112 | h11112
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11113 | h11113
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11114 | h11114
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11115 | h11115
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11116 | h11116
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11117 | h11117
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11118 | h11118
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11119 | h11119
                          · linarith only [h11025, h11028, h11119, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11121 | h11121
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11122 | h11122
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11123 | h11123
                                · rcases h0bigk with h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c | h11124c
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [hlam, p11124_0]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h0, hlam, p11124_1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h6793, hlam, p11124_0]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h10058, hlam, p11124_1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11028, h11114, h11117, h6793, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p11124_1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11024, hc15, hlam, hphi, ht0b, ht5b, p11124_1, u0elo1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [hlam, p11124_0]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11024, h11116, h11121, h11123, h6793, hc45, hlam, hphi, ht0b, ht5b, p11124_1, u0elo1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11024, h11028, h11116, h11121, h11123, h6793, hc45, hlam, hphi, ht0b, ht5b, p11124_1, u0elo1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    rcases p11124_3 (m.d 0 1) (by simp) with h11134 | h11134
                                    · linarith only [h0, h11134, hlam]
                                    · linarith only [h11024, h11134, hlam]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11024, h11116, h11121, h11123, hc45, hlam, hphi, ht0b, ht5b, p11124_1, u0elo2]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11025, hlam, p11124_1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [hlam, p11124_0]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11028, hlam, p11124_1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11024, h11028, h11114, h11116, h11117, h11121, h11123, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11124_1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11024, h11028, h11114, h11116, h11117, h11121, h11123, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11124_1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11026, hlam, p11124_0]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11024, h11028, h11114, h11116, h11117, h11121, h11123, h6793, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11124_1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [hlam, p11124_0]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    rcases p11124_3 (m.d 0 1) (by simp) with h11146 | h11146
                                    · linarith only [h10058, h11146, hlam]
                                    · linarith only [h11024, h11146, hlam]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11024, hlam, p11124_0]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11027, hlam, p11124_1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11112, hlam, p11124_0]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [h11113, hlam, p11124_1]
                                  · have p11124_0 := h11124c.1
                                    have p11124_1 := h11124c.2.1
                                    have p11124_2 := h11124c.2.2.1
                                    have p11124_3 := h11124c.2.2.2
                                    linarith only [hlam, p11124_0]
                                · linarith only [h11024, h11028, h11113, h11116, h11121, h11123, h6793, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                              · linarith only [h11024, h11028, h11114, h11117, h11118, h11122, h6793, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h11028, h11112, h11114, h11117, h11121, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h11028, h11113, h11117, h11118, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11158 | h11158
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11159 | h11159
                          · linarith only [h11117, h11159, h6793, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11161 | h11161
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11162 | h11162
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11163 | h11163
                                · rcases h0bigk with h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c | h11164c
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [hlam, p11164_0]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h0, hlam, p11164_1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h6793, hlam, p11164_0]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h10058, hlam, p11164_1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11024, h11116, h11117, h11161, h11163, h6793, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11164_1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11024, h11116, h11161, h11163, hc45, hlam, hphi, ht0b, ht5b, p11164_1, u0elo1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [hlam, p11164_0]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11024, h11116, h11161, h11163, h6793, hc45, hlam, hphi, ht0b, ht5b, p11164_1, u0elo1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h10058, h11024, h11116, h11161, h11163, hc45, hlam, hphi, ht0b, ht5b, p11164_1, u0elo1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    rcases p11164_3 (m.d 0 1) (by simp) with h11174 | h11174
                                    · linarith only [h0, h11174, hlam]
                                    · linarith only [h11024, h11174, hlam]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11024, h11116, h11161, h11163, hc45, hlam, hphi, ht0b, ht5b, p11164_1, u0elo2]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11025, hlam, p11164_1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [hlam, p11164_0]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11028, hlam, p11164_1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    rcases p11164_3 (m.d 0 1) (by simp) with h11181 | h11181
                                    · linarith only [h11181, h6793, hlam]
                                    · linarith only [h11024, h11181, hlam]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11024, h11026, h11116, h11161, h11163, hc45, hlam, hphi, ht0b, ht5b, p11164_1, u0elo1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11026, hlam, p11164_0]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11024, h11026, h11116, h11161, h11163, h6793, hc45, hlam, hphi, ht0b, ht5b, p11164_1, u0elo1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [hlam, p11164_0]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    rcases p11164_3 (m.d 0 1) (by simp) with h11188 | h11188
                                    · linarith only [h10058, h11188, hlam]
                                    · linarith only [h11024, h11188, hlam]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11024, hlam, p11164_0]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11027, hlam, p11164_1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11112, hlam, p11164_0]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [h11113, hlam, p11164_1]
                                  · have p11164_0 := h11164c.1
                                    have p11164_1 := h11164c.2.1
                                    have p11164_2 := h11164c.2.2.1
                                    have p11164_3 := h11164c.2.2.2
                                    linarith only [hlam, p11164_0]
                                · linarith only [h11117, h11163, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h11024, h11117, h11158, h11162, h6793, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h11112, h11117, h11161, h6793, hc23, hc34, hlam, hphi]
                        · linarith only [h10058, h11113, h11158, hlam]
                    · linarith only [h0, h11027, h11116, hlam]
                  · linarith only [h0, h11026, h11115, hlam]
                · linarith only [h0, h11025, h11114, hlam]
              · linarith only [h11024, h11028, h11113, h6793, hlam]
            · linarith only [h11024, h11112, h6793, hlam]
        · linarith only [h0, h11024, h11027, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h11206 | h11206
        · rcases m.htr 0 3 4 (by decide) (by decide) with h11207 | h11207
          · linarith only [h11025, h11026, h11207, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11209 | h11209
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11210 | h11210
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11211 | h11211
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11212 | h11212
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11213 | h11213
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11214 | h11214
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11215 | h11215
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11216 | h11216
                          · linarith only [h11025, h11026, h11207, h11212, h11216, h6793, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11218 | h11218
                            · linarith only [h11025, h11026, h11211, h11214, h11216, h11218, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h11025, h11026, h11209, h11211, h11214, h11216, h11218, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h10058, h11024, h11210, h11213, h11215, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11222 | h11222
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11223 | h11223
                          · linarith only [h11024, h11213, h11214, h11223, h6793, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11225 | h11225
                            · linarith only [h11025, h11026, h11212, h11225, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h11209, h11214, h11225, h6793, hc23, hc34, hlam, hphi]
                        · linarith only [h11025, h11026, h11212, h11222, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h11206, h11213, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11230 | h11230
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11231 | h11231
                      · linarith only [h11024, h11207, h11211, h11212, h11230, h11231, h6793, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11233 | h11233
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11234 | h11234
                          · linarith only [h10058, h11024, h11025, h11230, h11231, h11234, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11236 | h11236
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11237 | h11237
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11238 | h11238
                                · rcases h0bigk with h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c | h11239c
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [hlam, p11239_0]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h0, hlam, p11239_1]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h6793, hlam, p11239_0]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h10058, hlam, p11239_1]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h0, h11212, h11234, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11239_1]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h0, h11212, h11234, hc01, hc34, hlam, hphi, ht12, ht23, p11239_1]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [hlam, p11239_0]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h0, h11212, h11234, hc03, hc34, hlam, hphi, p11239_1]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h11026, hlam, p11239_1]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    rcases p11239_3 (m.d 0 1) (by simp) with h11249 | h11249
                                    · linarith only [h0, h11249, hlam]
                                    · linarith only [h11024, h11249, hlam]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h11024, h11230, h11236, h11238, hc45, hlam, hphi, ht0b, ht5b, p11239_1, u0elo2]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h11025, hlam, p11239_1]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [hlam, p11239_0]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h11207, hlam, p11239_1]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    rcases p11239_3 (m.d 0 1) (by simp) with h11256 | h11256
                                    · linarith only [h11256, h6793, hlam]
                                    · linarith only [h11024, h11256, hlam]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h11024, h11230, h11236, h11238, hc45, hlam, hphi, ht0b, ht5b, p11239_1, u0elo3]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h11025, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11239_1, u0elo3]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h11024, h11230, h11236, h11238, h6793, hc45, hlam, hphi, ht0b, ht5b, p11239_1, u0elo3]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [hlam, p11239_0]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    rcases p11239_3 (m.d 0 1) (by simp) with h11263 | h11263
                                    · linarith only [h10058, h11263, hlam]
                                    · linarith only [h11024, h11263, hlam]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h11024, hlam, p11239_0]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h11206, hlam, p11239_1]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h11209, hlam, p11239_0]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [h11210, hlam, p11239_1]
                                  · have p11239_0 := h11239c.1
                                    have p11239_1 := h11239c.2.1
                                    have p11239_2 := h11239c.2.2.1
                                    have p11239_3 := h11239c.2.2.2
                                    linarith only [hlam, p11239_0]
                                · linarith only [h11024, h11211, h11212, h11230, h11234, h11236, h11238, h6793, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                              · linarith only [h11024, h11211, h11212, h11233, h11237, h6793, hlam]
                            · linarith only [h11209, h11211, h11212, h11234, h11236, h6793, hc23, hc34, hlam, hphi]
                        · linarith only [h10058, h11210, h11233, hlam]
                    · linarith only [h0, h11206, h11230, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h11024, h11025, h11211, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
              · linarith only [h0, h11024, h11026, h11210, hlam]
            · linarith only [h11024, h11209, h6793, hlam]
        · linarith only [h11024, h11025, h11206, h6793, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h11280 | h11280
      · rcases m.htr 0 2 5 (by decide) (by decide) with h11281 | h11281
        · rcases m.htr 0 3 4 (by decide) (by decide) with h11282 | h11282
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11283 | h11283
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11284 | h11284
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11285 | h11285
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11286 | h11286
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11287 | h11287
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11288 | h11288
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11289 | h11289
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11290 | h11290
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11291 | h11291
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11292 | h11292
                              · linarith only [h11025, h11280, h11285, h11292, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h11025, h11280, h11284, h11285, h11292, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h10058, h11025, h11280, h11283, h11291, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h11025, h11282, h11290, hlam]
                        · linarith only [h10058, h11280, h11284, h11289, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h11025, h11280, h11282, h11285, h11288, hlam]
                    · linarith only [h11025, h11285, h11287, hc02, hc25, hlam, hphi]
                  · linarith only [h11025, h11280, h11285, h11286, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11301 | h11301
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11302 | h11302
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11303 | h11303
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11304 | h11304
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11305 | h11305
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11306 | h11306
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11307 | h11307
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11308 | h11308
                                · rcases h0bigk with h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c | h11309c
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [hlam, p11309_0]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h0, hlam, p11309_1]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h6793, hlam, p11309_0]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h10058, hlam, p11309_1]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h10058, h11285, h11301, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11309_1]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h11024, hc15, hlam, hphi, ht0b, ht5b, p11309_1, u0elo1]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [hlam, p11309_0]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h11025, hlam, p11309_0]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h0, h10058, h11024, h11285, h11302, h11306, h11308, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11309_1]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    rcases p11309_3 (m.d 0 1) (by simp) with h11319 | h11319
                                    · linarith only [h0, h11319, hlam]
                                    · linarith only [h11024, h11319, hlam]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h11024, h11302, h11306, h11308, hc45, hlam, hphi, ht0b, ht5b, p11309_1, u0elo2]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h0, h11024, h11302, h11306, h11308, hc45, hlam, hphi, ht0b, ht5b, p11309_1, u0elo2]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [hlam, p11309_0]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h10058, h11024, h11302, h11306, h11308, hc45, hlam, hphi, ht0b, ht5b, p11309_1, u0elo2]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    rcases p11309_3 (m.d 0 1) (by simp) with h11326 | h11326
                                    · linarith only [h11326, h6793, hlam]
                                    · linarith only [h11024, h11326, hlam]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h11024, h11302, h11306, h11308, hc45, hlam, hphi, ht0b, ht5b, p11309_1, u0elo3]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h11280, hlam, p11309_0]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h11282, hlam, p11309_0]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [hlam, p11309_0]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    rcases p11309_3 (m.d 0 1) (by simp) with h11333 | h11333
                                    · linarith only [h10058, h11333, hlam]
                                    · linarith only [h11024, h11333, hlam]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h11024, hlam, p11309_0]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h11281, hlam, p11309_1]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h11283, hlam, p11309_0]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [h11284, hlam, p11309_1]
                                  · have p11309_0 := h11309c.1
                                    have p11309_1 := h11309c.2.1
                                    have p11309_2 := h11309c.2.2.1
                                    have p11309_3 := h11309c.2.2.2
                                    linarith only [hlam, p11309_0]
                                · linarith only [h0, h11024, h11285, h11304, h11308, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h10058, h11024, h11285, h11301, h11304, h11307, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h10058, h11285, h11301, h11306, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h10058, h11285, h11301, h11305, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h10058, h11024, h11280, h11284, h11302, h11304, hc25, hlam, hphi, ht0b, ht5b, u0elo1]
                      · linarith only [h11282, h11303, h6793, hlam]
                    · linarith only [h0, h11281, h11302, hlam]
                  · linarith only [h0, h11280, h11301, hlam]
              · linarith only [h10058, h11024, h11284, hlam]
            · linarith only [h0, h11024, h11025, h11283, hlam]
          · linarith only [h11025, h11280, h11282, hlam]
        · linarith only [h10058, h11024, h11280, h11281, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h11353 | h11353
        · rcases m.htr 0 3 4 (by decide) (by decide) with h11354 | h11354
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11355 | h11355
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11356 | h11356
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11357 | h11357
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11358 | h11358
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11359 | h11359
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11360 | h11360
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11361 | h11361
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11362 | h11362
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11363 | h11363
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11364 | h11364
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11365 | h11365
                                · rcases h0bigk with h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c | h11366c
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [hlam, p11366_0]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h0, hlam, p11366_1]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h6793, hlam, p11366_0]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h10058, hlam, p11366_1]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h0, h11280, h11357, h11362, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p11366_1]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h11280, h11357, h11362, hc01, hc12, hlam, hphi, p11366_1]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [hlam, p11366_0]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h11025, hlam, p11366_0]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h11280, hlam, p11366_1]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h11024, h11280, h11357, h11359, h11362, h11363, h11365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11366_1]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h11024, h11359, h11363, h11365, hc45, hlam, hphi, ht0b, ht5b, p11366_1, u0elo2]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h0, h11024, h11025, h11357, h11359, h11363, h11365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11366_1]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [hlam, p11366_0]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h0, h11024, h11025, h11280, h11357, h11359, h11363, h11365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11366_1]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    rcases p11366_3 (m.d 0 1) (by simp) with h11381 | h11381
                                    · linarith only [h11381, h6793, hlam]
                                    · linarith only [h11024, h11381, hlam]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h11024, h11359, h11363, h11365, hc45, hlam, hphi, ht0b, ht5b, p11366_1, u0elo3]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h0, h11024, h11280, h11357, h11359, h11362, h11363, h11365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11366_1]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h11354, hlam, p11366_0]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [hlam, p11366_0]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    rcases p11366_3 (m.d 0 1) (by simp) with h11388 | h11388
                                    · linarith only [h10058, h11388, hlam]
                                    · linarith only [h11024, h11388, hlam]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h11024, hlam, p11366_0]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h11353, hlam, p11366_1]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h11355, hlam, p11366_0]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [h11356, hlam, p11366_1]
                                  · have p11366_0 := h11366c.1
                                    have p11366_1 := h11366c.2.1
                                    have p11366_2 := h11366c.2.2.1
                                    have p11366_3 := h11366c.2.2.2
                                    linarith only [hlam, p11366_0]
                                · linarith only [h0, h11024, h11280, h11357, h11361, h11362, h11365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h11024, h11280, h11361, h11364, hlam]
                            · linarith only [h11025, h11355, h11363, hlam]
                          · linarith only [h11025, h11354, h11362, hlam]
                        · linarith only [h10058, h11354, h11356, h11361, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h11024, h11025, h11354, h11357, h11359, h11360, h6793, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h11025, h11357, h11359, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h11025, h11357, h11358, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11404 | h11404
                  · linarith only [h0, h11024, h11280, h11357, h11404, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11406 | h11406
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11407 | h11407
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11408 | h11408
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11409 | h11409
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11410 | h11410
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11411 | h11411
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11412 | h11412
                                · rcases h0bigk with h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c | h11413c
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [hlam, p11413_0]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h0, hlam, p11413_1]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h6793, hlam, p11413_0]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h10058, hlam, p11413_1]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h0, h11404, h11409, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11413_1]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h0, h11404, h11409, hc01, hc23, hlam, hphi, ht12, p11413_1]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [hlam, p11413_0]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h11025, hlam, p11413_0]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h11280, hlam, p11413_1]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    rcases p11413_3 (m.d 0 1) (by simp) with h11423 | h11423
                                    · linarith only [h0, h11423, hlam]
                                    · linarith only [h11024, h11423, hlam]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h11024, h11406, h11410, h11412, hc45, hlam, hphi, ht0b, ht5b, p11413_1, u0elo2]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h0, h11024, h11406, h11410, h11412, hc45, hlam, hphi, ht0b, ht5b, p11413_1, u0elo2]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [hlam, p11413_0]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h10058, h11024, h11406, h11410, h11412, hc45, hlam, hphi, ht0b, ht5b, p11413_1, u0elo2]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    rcases p11413_3 (m.d 0 1) (by simp) with h11430 | h11430
                                    · linarith only [h11430, h6793, hlam]
                                    · linarith only [h11024, h11430, hlam]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h11024, h11406, h11410, h11412, hc45, hlam, hphi, ht0b, ht5b, p11413_1, u0elo3]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h0, h11024, h11406, h11410, h11412, hc45, hlam, hphi, ht0b, ht5b, p11413_1, u0elo3]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h11354, hlam, p11413_0]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [hlam, p11413_0]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    rcases p11413_3 (m.d 0 1) (by simp) with h11437 | h11437
                                    · linarith only [h10058, h11437, hlam]
                                    · linarith only [h11024, h11437, hlam]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h11024, hlam, p11413_0]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h11353, hlam, p11413_1]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h11355, hlam, p11413_0]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [h11356, hlam, p11413_1]
                                  · have p11413_0 := h11413c.1
                                    have p11413_1 := h11413c.2.1
                                    have p11413_2 := h11413c.2.2.1
                                    have p11413_3 := h11413c.2.2.2
                                    linarith only [hlam, p11413_0]
                                · linarith only [h0, h11024, h11404, h11408, h11409, h11412, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h11024, h11404, h11408, h11411, hlam]
                            · linarith only [h0, h11404, h11409, h11410, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h11354, h11357, h11409, h6793, hlam]
                        · linarith only [h0, h11354, h11356, h11404, h11408, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h11354, h11407, h6793, hlam]
                    · linarith only [h0, h11353, h11406, hlam]
              · linarith only [h0, h11024, h11280, h11356, hlam]
            · linarith only [h11024, h11355, h6793, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h11454 | h11454
            · rcases m.htr 0 4 5 (by decide) (by decide) with h11455 | h11455
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11456 | h11456
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11457 | h11457
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11458 | h11458
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11459 | h11459
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11460 | h11460
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11461 | h11461
                          · linarith only [h0, h11024, h11025, h11354, h11456, h11458, h11461, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h11024, h11025, h11458, h11459, h11461, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h10058, h11024, h11455, h11458, h11460, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11465 | h11465
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11466 | h11466
                          · linarith only [h11024, h11458, h11459, h11466, h6793, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11468 | h11468
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11469 | h11469
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11470 | h11470
                                · rcases h0bigk with h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c | h11471c
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [hlam, p11471_0]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h0, hlam, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h6793, hlam, p11471_0]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h10058, hlam, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h0, h11025, h11456, h11459, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11025, h11456, hc01, hc13, hlam, hphi, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [hlam, p11471_0]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11025, hlam, p11471_0]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11280, hlam, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11024, h11025, h11456, h11458, h11459, h11468, h11470, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11024, h11458, h11468, h11470, hc45, hlam, hphi, ht0b, ht5b, p11471_1, u0elo2]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11025, h11456, h11459, hc02, hc34, hlam, hphi, ht23, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [hlam, p11471_0]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11354, hlam, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    rcases p11471_3 (m.d 0 1) (by simp) with h11486 | h11486
                                    · linarith only [h11486, h6793, hlam]
                                    · linarith only [h11024, h11486, hlam]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11024, h11280, h11457, h11458, h11468, h11470, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h0, h11024, h11280, h11457, h11458, h11468, h11470, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11024, h11280, h11457, h11458, h11468, h11470, h6793, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [hlam, p11471_0]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    rcases p11471_3 (m.d 0 1) (by simp) with h11493 | h11493
                                    · linarith only [h10058, h11493, hlam]
                                    · linarith only [h11024, h11493, hlam]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11024, hlam, p11471_0]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11353, hlam, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11454, hlam, p11471_0]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [h11455, hlam, p11471_1]
                                  · have p11471_0 := h11471c.1
                                    have p11471_1 := h11471c.2.1
                                    have p11471_2 := h11471c.2.2.1
                                    have p11471_3 := h11471c.2.2.2
                                    linarith only [hlam, p11471_0]
                                · linarith only [h11459, h11470, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h0, h11024, h11025, h11280, h11456, h11459, h11465, h11469, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h11025, h11454, h11468, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h11280, h11455, h11457, h11465, hlam]
                    · linarith only [h0, h11353, h11458, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h11025, h11456, h11457, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h11507 | h11507
                  · linarith only [h0, h11024, h11280, h11456, h11507, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11509 | h11509
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11510 | h11510
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11511 | h11511
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11512 | h11512
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h11513 | h11513
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h11514 | h11514
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h11515 | h11515
                                · rcases h0bigk with h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c | h11516c
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [hlam, p11516_0]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h0, hlam, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h6793, hlam, p11516_0]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h10058, hlam, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h0, h11024, h11507, h11509, h11512, h11513, h11515, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h0, h11507, h11512, hc01, hc23, hlam, hphi, ht12, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [hlam, p11516_0]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11025, hlam, p11516_0]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11280, hlam, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11024, h11025, h11354, h11456, h11509, h11510, h11513, h11515, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11024, h11354, h11456, h11509, h11510, h11513, h11515, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11354, h11456, h11510, hc02, hc23, hlam, hphi, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [hlam, p11516_0]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11354, hlam, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11024, h11354, h11456, h11509, h11510, h11513, h11515, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11024, h11354, h11456, h11509, h11510, h11513, h11515, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h0, h11024, h11354, h11456, h11509, h11510, h11513, h11515, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11024, h11354, h11456, h11509, h11510, h11513, h11515, h6793, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [hlam, p11516_0]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    rcases p11516_3 (m.d 0 1) (by simp) with h11536 | h11536
                                    · linarith only [h10058, h11536, hlam]
                                    · linarith only [h11024, h11536, hlam]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11024, hlam, p11516_0]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11353, hlam, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11454, hlam, p11516_0]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [h11455, hlam, p11516_1]
                                  · have p11516_0 := h11516c.1
                                    have p11516_1 := h11516c.2.1
                                    have p11516_2 := h11516c.2.2.1
                                    have p11516_3 := h11516c.2.2.2
                                    linarith only [hlam, p11516_0]
                                · linarith only [h0, h11025, h11354, h11455, h11515, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h0, h11024, h11507, h11511, h11514, hlam]
                            · linarith only [h0, h11025, h11354, h11456, h11510, h11513, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h11456, h11510, h11512, hlam]
                        · linarith only [h11354, h11455, h11510, h11511, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h11549 | h11549
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h11550 | h11550
                          · linarith only [h0, h11456, h11510, h11550, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h11024, h11456, h11509, h11550, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h10058, h11455, h11549, hlam]
                    · linarith only [h0, h11353, h11509, hlam]
              · linarith only [h10058, h11024, h11455, hlam]
            · linarith only [h0, h11024, h11025, h11454, hlam]
        · linarith only [h0, h11024, h11353, hlam]
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s12 m hb0 hb2 hb4 h0 h6793 h10058 h11024

end R2N4
