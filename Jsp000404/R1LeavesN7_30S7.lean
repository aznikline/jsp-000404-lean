import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_30S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2475 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2881 | h2881
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2882 | h2882
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2883 | h2883
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2884 | h2884
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2885 | h2885
          · linarith only [h2474, h2475, h2885, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2887 | h2887
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2888 | h2888
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2889 | h2889
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2890 | h2890
                  · linarith only [h2474, h2885, h2887, h2889, h2890, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases h0bigk with h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c | h2892c
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [hlam, p2892_0]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h0, hlam, p2892_1]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h0, h2887, hc12, hlam, hphi, ht01, ht0b, ht5b, p2892_1, u5ehi3]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2475, hlam, p2892_1]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2892_1, u5ehi0]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2892_1]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [hlam, p2892_0]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h0, h2887, hc12, hlam, hphi, ht01, ht0b, ht5b, p2892_1, u5ehi3]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h0, h2474, h2475, h2887, hc12, hlam, hphi, ht01, ht0b, ht5b, p2892_1, u5ehi3]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h0, h2884, hc12, hlam, hphi, ht01, ht0b, ht5b, p2892_1, u5ehi2]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2474, hlam, p2892_1]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2882, hlam, p2892_1]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [hlam, p2892_0]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2885, hlam, p2892_1]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2474, h2884, hc01, hlam, hphi, ht0b, ht5b, p2892_1, u5ehi2]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2474, h2889, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2892_1]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2883, hlam, p2892_0]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2885, hc03, hc34, hlam, hphi, p2892_1]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [hlam, p2892_0]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2884, h2885, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2892_1, u5ehi2]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2881, hlam, p2892_0]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2884, hlam, p2892_1]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2887, hlam, p2892_0]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [h2888, hlam, p2892_1]
                    · have p2892_0 := h2892c.1
                      have p2892_1 := h2892c.2.1
                      have p2892_2 := h2892c.2.2.1
                      have p2892_3 := h2892c.2.2.2
                      linarith only [hlam, p2892_0]
                · linarith only [h0, h2474, h2887, h2889, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h2475, h2881, h2888, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2920 | h2920
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2921 | h2921
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2922 | h2922
                  · linarith only [h0, h2474, h2885, h2921, h2922, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c | h2924c
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [hlam, p2924_0]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h0, hlam, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h0, h2474, h2921, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2475, hlam, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p2924_1, u5ehi0]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [hlam, p2924_0]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      rcases p2924_3 (m.d 0 1) (by simp) with h2932 | h2932
                      · linarith only [h0, h2932, hlam]
                      · linarith only [h2474, h2932, hlam]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h0, h2475, h2881, hc12, hlam, hphi, ht01, ht0b, ht5b, p2924_1, u5ehi1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h0, h2881, hc12, hlam, hphi, ht01, ht0b, ht5b, p2924_1, u5ehi1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2474, hlam, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2882, hlam, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [hlam, p2924_0]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2885, hlam, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2887, hlam, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2881, hc04, hlam, hphi, ht0b, ht5b, p2924_1, u5ehi1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2883, hlam, p2924_0]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2474, h2885, h2921, hc23, hc34, hlam, hphi, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [hlam, p2924_0]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2881, h2885, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2924_1, u5ehi1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2881, hlam, p2924_0]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2884, hlam, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h0, h2474, h2881, h2921, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [h2920, hlam, p2924_1]
                    · have p2924_0 := h2924c.1
                      have p2924_1 := h2924c.2.1
                      have p2924_2 := h2924c.2.2.1
                      have p2924_3 := h2924c.2.2.2
                      linarith only [hlam, p2924_0]
                · linarith only [h0, h2881, h2921, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h2475, h2881, h2920, hlam]
        · linarith only [h0, h2881, h2884, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2955 | h2955
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2956 | h2956
          · linarith only [h0, h2474, h2883, h2956, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2958 | h2958
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2959 | h2959
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2960 | h2960
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2961 | h2961
                  · linarith only [h2474, h2475, h2956, h2960, h2961, hlam]
                  · rcases h0bigk with h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c | h2963c
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [hlam, p2963_0]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h0, hlam, p2963_1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h0, h2883, h2958, h2961, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2963_1, u5ehi3]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2475, hlam, p2963_1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h0, h2883, h2961, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2963_1, u5ehi0]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2883, h2961, hc01, hc34, hlam, hphi, ht12, ht23, p2963_1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [hlam, p2963_0]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2883, h2958, h2961, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2963_1, u5ehi3]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2883, hlam, p2963_1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2881, h2883, h2961, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2963_1, u5ehi1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2474, hlam, p2963_1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2882, hlam, p2963_1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [hlam, p2963_0]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2956, hlam, p2963_1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2474, h2881, hc01, hlam, hphi, ht0b, ht5b, p2963_1, u5ehi1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2474, h2960, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2963_1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h0, h2881, h2883, h2961, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2963_1, u5ehi1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2883, h2961, hc03, hc34, hlam, hphi, p2963_1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [hlam, p2963_0]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2881, h2883, h2961, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2963_1, u5ehi1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2881, hlam, p2963_0]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2955, hlam, p2963_1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2958, hlam, p2963_0]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [h2959, hlam, p2963_1]
                    · have p2963_0 := h2963c.1
                      have p2963_1 := h2963c.2.1
                      have p2963_2 := h2963c.2.2.1
                      have p2963_3 := h2963c.2.2.2
                      linarith only [hlam, p2963_0]
                · linarith only [h0, h2474, h2958, h2960, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h2475, h2881, h2959, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2991 | h2991
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2992 | h2992
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2993 | h2993
                  · linarith only [h0, h2474, h2956, h2992, h2993, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c | h2995c
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [hlam, p2995_0]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h0, hlam, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h0, h2474, h2883, h2992, h2993, hc23, hc34, hlam, hphi, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2475, hlam, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h0, h2883, h2993, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2995_1, u5ehi0]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2883, h2993, hc01, hc34, hlam, hphi, ht12, ht23, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [hlam, p2995_0]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2474, h2883, h2992, h2993, hc23, hc34, hlam, hphi, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2883, hlam, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2883, h2991, h2993, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2995_1, u5ehi4]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2474, hlam, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2882, hlam, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [hlam, p2995_0]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2956, hlam, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2958, hlam, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2881, h2883, h2993, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2995_1, u5ehi1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2883, h2993, hc02, hc34, hlam, hphi, ht23, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2474, h2883, h2992, h2993, hc23, hc34, hlam, hphi, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [hlam, p2995_0]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2883, h2991, h2993, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2995_1, u5ehi4]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2881, hlam, p2995_0]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2955, hlam, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h0, h2474, h2881, h2992, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [h2991, hlam, p2995_1]
                    · have p2995_0 := h2995c.1
                      have p2995_1 := h2995c.2.1
                      have p2995_2 := h2995c.2.2.1
                      have p2995_3 := h2995c.2.2.2
                      linarith only [hlam, p2995_0]
                · linarith only [h0, h2881, h2992, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h2881, h2883, h2991, hlam]
        · linarith only [h0, h2881, h2955, hlam]
    · linarith only [h0, h2474, h2882, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3025 | h3025
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3026 | h3026
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3027 | h3027
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3028 | h3028
          · linarith only [h2474, h2475, h3028, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3030 | h3030
            · linarith only [h2474, h2881, h3030, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3032 | h3032
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3033 | h3033
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3034 | h3034
                  · linarith only [h0, h2474, h3028, h3033, h3034, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c | h3036c
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [hlam, p3036_0]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h0, hlam, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h0, h2474, h3033, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h2475, hlam, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h2881, hlam, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [hlam, p3036_0]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      rcases p3036_3 (m.d 0 1) (by simp) with h3044 | h3044
                      · linarith only [h0, h3044, hlam]
                      · linarith only [h2474, h3044, hlam]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h0, h3032, hc12, hlam, hphi, ht01, ht0b, ht5b, p3036_1, u5ehi4]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h0, h2474, h2881, h3033, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h2474, hlam, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h3025, hlam, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [hlam, p3036_0]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h3028, hlam, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h3030, hlam, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h2474, h3033, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h3026, hlam, p3036_0]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h2474, h3028, h3033, hc23, hc34, hlam, hphi, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [hlam, p3036_0]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h2474, h2881, h3028, h3033, hc23, hc34, hlam, hphi, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h2474, h3033, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h3027, hlam, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h2474, h3030, h3033, hc23, hc35, hlam, hphi, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [h3032, hlam, p3036_1]
                    · have p3036_0 := h3036c.1
                      have p3036_1 := h3036c.2.1
                      have p3036_2 := h3036c.2.2.1
                      have p3036_3 := h3036c.2.2.2
                      linarith only [hlam, p3036_0]
                · linarith only [h0, h2474, h3025, h3033, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3065 | h3065
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3066 | h3066
                  · linarith only [h2474, h2475, h3032, h3065, h3066, hc34, hc45, hlam, hphi]
                  · rcases h0bigk with h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c | h3068c
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [hlam, p3068_0]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h0, hlam, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h2475, h3032, hc03, hc45, hlam, hphi, ht34, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h2475, hlam, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h2881, hlam, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [hlam, p3068_0]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      rcases p3068_3 (m.d 0 1) (by simp) with h3076 | h3076
                      · linarith only [h0, h3076, hlam]
                      · linarith only [h2474, h3076, hlam]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h0, h2474, h2475, h3065, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3068_1, u5ehi0]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h2474, hlam, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h3025, hlam, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [hlam, p3068_0]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h3028, hlam, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h3030, hlam, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h2474, h3065, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h3026, hlam, p3068_0]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h2474, h3028, h3065, hc23, hc34, hlam, hphi, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [hlam, p3068_0]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h3032, hlam, p3068_0]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h2474, h3065, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h3027, hlam, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h2474, h3030, h3065, hc23, hc35, hlam, hphi, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [h3032, hc04, hc45, hlam, hphi, p3068_1]
                    · have p3068_0 := h3068c.1
                      have p3068_1 := h3068c.2.1
                      have p3068_2 := h3068c.2.2.1
                      have p3068_3 := h3068c.2.2.2
                      linarith only [hlam, p3068_0]
                · linarith only [h0, h2474, h3025, h3065, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3097 | h3097
          · linarith only [h2474, h2475, h3097, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3099 | h3099
            · linarith only [h2474, h2881, h3099, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3101 | h3101
              · linarith only [h3026, h3027, h3101, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3103 | h3103
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3104 | h3104
                  · linarith only [h0, h2474, h3097, h3103, h3104, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c | h3106c
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [hlam, p3106_0]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h0, hlam, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h2474, h2475, h3101, h3103, hc23, hc45, hlam, hphi, ht34, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h2475, hlam, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h2881, hlam, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h3027, hc01, hc25, hlam, hphi, ht12, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [hlam, p3106_0]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h2474, h3027, h3103, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h3027, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h3027, hlam, p3106_0]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h2474, hlam, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h3025, hlam, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [hlam, p3106_0]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h3097, hlam, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h3099, hlam, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h2474, h3103, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h3026, hlam, p3106_0]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h2474, h3026, h3027, h3103, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [hlam, p3106_0]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h3101, hlam, p3106_0]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h2474, h3103, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h3099, hc02, hc35, hlam, hphi, ht23, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h2474, h3099, h3103, hc23, hc35, hlam, hphi, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [h2474, h2475, h3101, h3103, hc23, hc45, hlam, hphi, ht34, p3106_1]
                    · have p3106_0 := h3106c.1
                      have p3106_1 := h3106c.2.1
                      have p3106_2 := h3106c.2.2.1
                      have p3106_3 := h3106c.2.2.2
                      linarith only [hlam, p3106_0]
                · linarith only [h0, h3025, h3103, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3133 | h3133
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3134 | h3134
          · linarith only [h0, h2474, h3026, h3134, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3136 | h3136
            · linarith only [h2474, h2881, h3136, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3138 | h3138
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3139 | h3139
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3140 | h3140
                  · linarith only [h2474, h2881, h3026, h3133, h3134, h3139, h3140, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases h0bigk with h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c | h3142c
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [hlam, p3142_0]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h0, hlam, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h2474, h2881, h3026, h3133, h3139, h3140, hc23, hc34, hlam, hphi, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h2475, hlam, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h2881, hlam, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h3026, h3140, hc01, hc34, hlam, hphi, ht12, ht23, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [hlam, p3142_0]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h2474, h3026, h3139, h3140, hc23, hc34, hlam, hphi, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h3026, hlam, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h3026, h3140, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3142_1, u5ehi0]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h2474, hlam, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h3025, hlam, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [hlam, p3142_0]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h3134, hlam, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h3136, hlam, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h2474, h3139, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h3026, h3140, hc02, hc34, hlam, hphi, ht23, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h2474, h3026, h3139, h3140, hc23, hc34, hlam, hphi, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [hlam, p3142_0]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h2474, h2881, h3026, h3139, h3140, hc23, hc34, hlam, hphi, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h2474, h3139, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h3133, hlam, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h2474, h3026, h3133, h3139, h3140, hc23, hc34, hlam, hphi, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [h3138, hlam, p3142_1]
                    · have p3142_0 := h3142c.1
                      have p3142_1 := h3142c.2.1
                      have p3142_2 := h3142c.2.2.1
                      have p3142_3 := h3142c.2.2.2
                      linarith only [hlam, p3142_0]
                · linarith only [h0, h3025, h3139, hlam]
              · linarith only [h3026, h3133, h3138, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3170 | h3170
          · linarith only [h0, h2474, h3026, h3170, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3172 | h3172
            · linarith only [h0, h2474, h3133, h3172, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3174 | h3174
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3175 | h3175
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3176 | h3176
                  · linarith only [h0, h2474, h3170, h3175, h3176, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases h0bigk with h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c | h3178c
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [hlam, p3178_0]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h0, hlam, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h0, h2474, h3026, h3175, h3176, hc23, hc34, hlam, hphi, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h2475, hlam, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h2881, hlam, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h3026, h3176, hc01, hc34, hlam, hphi, ht12, ht23, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [hlam, p3178_0]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h2474, h3026, h3175, h3176, hc23, hc34, hlam, hphi, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h3026, hlam, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h3133, hlam, p3178_0]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h2474, hlam, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h3025, hlam, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [hlam, p3178_0]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h3170, hlam, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h3172, hlam, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h2474, h3175, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h3026, h3176, hc02, hc34, hlam, hphi, ht23, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h2474, h3026, h3175, h3176, hc23, hc34, hlam, hphi, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [hlam, p3178_0]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h0, h2474, h3026, h3133, h3175, h3176, hc23, hc34, hlam, hphi, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h2474, h3175, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h0, h2474, h3172, h3175, hc23, hc35, hlam, hphi, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h2474, h3172, h3175, hc23, hc35, hlam, hphi, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [h3174, hlam, p3178_1]
                    · have p3178_0 := h3178c.1
                      have p3178_1 := h3178c.2.1
                      have p3178_2 := h3178c.2.2.1
                      have p3178_3 := h3178c.2.2.2
                      linarith only [hlam, p3178_0]
                · linarith only [h0, h3025, h3175, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3205 | h3205
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3206 | h3206
                  · linarith only [h0, h2474, h3026, h3174, h3205, h3206, hc34, hc45, hlam, hphi]
                  · rcases h0bigk with h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c | h3208c
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [hlam, p3208_0]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h0, hlam, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h0, h3026, h3174, hc03, hc45, hlam, hphi, ht34, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h2475, hlam, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h2881, hlam, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h3026, h3174, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [hlam, p3208_0]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h2474, h3026, h3174, h3205, hc23, hc45, hlam, hphi, ht34, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h3026, hlam, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h3133, hlam, p3208_0]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h2474, hlam, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h3025, hlam, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [hlam, p3208_0]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h3170, hlam, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h3172, hlam, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h2474, h3174, h3205, hc23, hc45, hlam, hphi, ht34, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h3174, hc02, hc45, hlam, hphi, ht23, ht34, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h2474, h3174, h3205, hc23, hc45, hlam, hphi, ht34, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [hlam, p3208_0]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h3174, hlam, p3208_0]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h2474, h3205, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h0, h2474, h3133, h3205, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h2474, h3172, h3205, hc23, hc35, hlam, hphi, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [h3174, hc04, hc45, hlam, hphi, p3208_1]
                    · have p3208_0 := h3208c.1
                      have p3208_1 := h3208c.2.1
                      have p3208_2 := h3208c.2.2.1
                      have p3208_3 := h3208c.2.2.2
                      linarith only [hlam, p3208_0]
                · linarith only [h0, h2474, h3025, h3205, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h2474, h3025, hlam]

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2475 | h2475
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x0_x0 m hb0 hb2 hb3 hb5 h0 h2474 h2475
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x0_x1 m hb0 hb2 hb3 hb5 h0 h2474 h2475

end R2N4
