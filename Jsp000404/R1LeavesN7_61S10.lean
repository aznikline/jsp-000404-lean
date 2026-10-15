import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_61S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3294000 in
set_option maxHeartbeats 3294000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h876 | h876
  · rcases m.htr 0 1 5 (by decide) (by decide) with h877 | h877
    · rcases m.htr 0 2 3 (by decide) (by decide) with h878 | h878
      · linarith only [h0, h1, h878, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h880 | h880
        · rcases m.htr 0 2 5 (by decide) (by decide) with h881 | h881
          · linarith only [h878, h881, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h883 | h883
            · rcases m.htr 0 3 5 (by decide) (by decide) with h884 | h884
              · rcases m.htr 0 4 5 (by decide) (by decide) with h885 | h885
                · linarith only [h878, h880, h885, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h887 | h887
                  · linarith only [h881, h887, hc02, hlam, hphi, u2elo1]
                  · rcases h0bigk with h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c | h889c
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h880, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h1, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h1, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h1, hc13, hlam, hphi, ht01, ht0b, ht5b, p889_1, u5ehi0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h0, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h878, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h876, h881, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p889_1, u2elo4]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h881, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h878, hc01, hlam, hphi, ht12, p889_1, u2elo2]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h878, hc02, hlam, hphi, p889_1, u2elo2]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h876, h878, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p889_1, u2elo2]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h878, h880, h881, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p889_1, u2elo2]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h876, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h880, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h883, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h885, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h877, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h880, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p889_1]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h884, hlam, p889_0]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [h1, h876, h877, h878, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p889_1, u2elo2]
                    · have p889_0 := h889c.1
                      have p889_1 := h889c.2.1
                      have p889_2 := h889c.2.2.1
                      have p889_3 := h889c.2.2.2
                      linarith only [hlam, p889_0]
              · linarith only [h1, h877, h884, hlam]
            · linarith only [h1, h876, h883, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h917 | h917
          · linarith only [h878, h917, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h919 | h919
            · rcases m.htr 0 3 5 (by decide) (by decide) with h920 | h920
              · rcases m.htr 0 4 5 (by decide) (by decide) with h921 | h921
                · rcases m.htr 1 2 5 (by decide) (by decide) with h922 | h922
                  · linarith only [h917, h922, hc02, hlam, hphi, u2elo1]
                  · rcases h0bigk with h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c | h924c
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h0, h1, h878, hc12, hlam, hphi, p924_1, u2elo2]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h1, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h1, h878, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p924_1, u2elo2]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h1, h878, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1, u2elo2, u5ehi0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h0, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h878, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h880, hlam, p924_1]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h917, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h878, hc01, hlam, hphi, ht12, p924_1, u2elo2]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h0, h878, hc12, hlam, hphi, p924_1, u2elo2]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h878, h921, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1, u2elo2, u5ehi4]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h877, h878, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1, u2elo2, u5ehi1]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h876, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h0, h880, hc12, hlam, hphi, p924_1, u2elo3]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h919, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h1, h876, h877, h878, hlam, hphi, ht01, ht0b, ht12, ht5b, p924_1, u2elo2, u5ehi1]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h877, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h0, h1, h877, h878, hc12, hlam, hphi, p924_1, u2elo2]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h920, hlam, p924_0]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [h921, hlam, p924_1]
                    · have p924_0 := h924c.1
                      have p924_1 := h924c.2.1
                      have p924_2 := h924c.2.2.1
                      have p924_3 := h924c.2.2.2
                      linarith only [hlam, p924_0]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h950 | h950
                  · linarith only [h0, h1, h878, h917, h950, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                  · rcases h0bigk with h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c | h952c
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h1, h878, hc02, hlam, hphi, p952_1, u2elo2]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h1, hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h1, h878, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p952_1, u2elo2]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h1, h878, hlam, hphi, ht01, ht0b, ht12, ht5b, p952_1, u2elo2, u5ehi0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h0, hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h878, hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h880, hlam, p952_1]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h917, hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h878, hc01, hlam, hphi, ht12, p952_1, u2elo2]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h0, h878, hc12, hlam, hphi, p952_1, u2elo2]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h0, h878, h880, hc12, hlam, hphi, p952_1, u2elo2]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h878, h920, hlam, hphi, ht01, ht0b, ht12, ht5b, p952_1, u2elo2, u5ehi3]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h876, hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h0, h921, hc12, hc45, hlam, hphi, ht23, ht34, p952_1]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h919, hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h921, hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h877, hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h0, h1, h877, h878, hc12, hlam, hphi, p952_1, u2elo2]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h920, hlam, p952_0]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [h1, h877, h878, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p952_1, u2elo2]
                    · have p952_0 := h952c.1
                      have p952_1 := h952c.2.1
                      have p952_2 := h952c.2.2.1
                      have p952_3 := h952c.2.2.2
                      linarith only [hlam, p952_0]
              · linarith only [h1, h877, h920, hlam]
            · linarith only [h1, h876, h919, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h980 | h980
      · linarith only [h0, h1, h980, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h982 | h982
        · rcases m.htr 0 2 5 (by decide) (by decide) with h983 | h983
          · linarith only [h980, h983, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h985 | h985
            · rcases m.htr 0 3 5 (by decide) (by decide) with h986 | h986
              · rcases m.htr 0 4 5 (by decide) (by decide) with h987 | h987
                · linarith only [h980, h982, h987, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h989 | h989
                  · linarith only [h983, h989, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h877, h989, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h992 | h992
                · linarith only [h980, h982, h992, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h994 | h994
                  · linarith only [h0, h1, h983, h986, h994, hlam]
                  · linarith only [h0, h877, h994, hc12, hlam, hphi, u2elo4]
            · linarith only [h0, h1, h980, h982, h985, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h998 | h998
          · linarith only [h982, h998, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1000 | h1000
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1001 | h1001
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1002 | h1002
                · linarith only [h1002, h876, h877, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1004 | h1004
                  · linarith only [h0, h1004, h877, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h1004, h877, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1007 | h1007
                · linarith only [h1, h1001, h1007, h876, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1009 | h1009
                  · linarith only [h0, h1, h1001, h1009, h998, hlam]
                  · linarith only [h0, h1009, h877, hc12, hlam, hphi, u2elo4]
            · linarith only [h1, h1000, h876, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1013 | h1013
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1014 | h1014
      · linarith only [h0, h1, h1014, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1016 | h1016
        · linarith only [h1013, h1014, h1016, h876, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1018 | h1018
          · linarith only [h1014, h1018, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1020 | h1020
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1021 | h1021
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1022 | h1022
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1023 | h1023
                  · linarith only [h1018, h1023, hc02, hlam, hphi, u2elo1]
                  · rcases h0bigk with h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [hlam, p1025_0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h0, h876, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1025_1]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1, hlam, p1025_0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h876, hlam, p1025_1]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1016, h876, hlam, hphi, ht01, ht0b, ht12, ht5b, p1025_1, u2elo3, u5ehi0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h0, hlam, p1025_0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [hlam, p1025_0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1014, hlam, p1025_0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1016, hlam, p1025_1]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1018, hlam, p1025_0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1025_1]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h0, h1014, hc12, hlam, hphi, p1025_1, u2elo2]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [hlam, p1025_0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1014, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1025_1, u2elo2]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1013, h1014, hlam, hphi, ht01, ht0b, ht12, ht5b, p1025_1, u2elo2, u5ehi1]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1013, hc04, hlam, hphi, ht0b, ht5b, p1025_1, u5ehi1]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h0, h1016, hc12, hlam, hphi, p1025_1, u2elo3]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1020, hlam, p1025_0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [hlam, p1025_0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1013, h1014, h1020, hlam, hphi, ht01, ht0b, ht12, ht5b, p1025_1, u2elo2, u5ehi1]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1013, hlam, p1025_0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h0, h1, h1013, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1025_1]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1021, hlam, p1025_0]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [h1022, hlam, p1025_1]
                    · have p1025_0 := h1025c.1
                      have p1025_1 := h1025c.2.1
                      have p1025_2 := h1025c.2.2.1
                      have p1025_3 := h1025c.2.2.2
                      linarith only [hlam, p1025_0]
                · linarith only [h1013, h1022, h876, hlam]
              · linarith only [h1013, h1020, h1021, h876, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1053 | h1053
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1054 | h1054
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1055 | h1055
                  · linarith only [h0, h1, h1018, h1020, h1055, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                  · rcases h0bigk with h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c | h1057c
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [hlam, p1057_0]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1, h1016, h1020, hc02, hlam, hphi, p1057_1, u2elo3]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1, hlam, p1057_0]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h876, hlam, p1057_1]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1, h1016, h1020, h1053, hlam, hphi, ht01, ht0b, ht12, ht5b, p1057_1, u2elo3, u5ehi3]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h0, hlam, p1057_0]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [hlam, p1057_0]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1014, hlam, p1057_0]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1016, hlam, p1057_1]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1018, hlam, p1057_0]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1016, h1020, hc01, hlam, hphi, ht12, p1057_1, u2elo3]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h0, h1016, h1020, hc12, hlam, hphi, p1057_1, u2elo3]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [hlam, p1057_0]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1020, hlam, p1057_1]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1016, h1020, h1053, hlam, hphi, ht01, ht0b, ht12, ht5b, p1057_1, u2elo3, u5ehi3]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1013, h1016, hlam, hphi, ht01, ht0b, ht12, ht5b, p1057_1, u2elo3, u5ehi1]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h0, h1016, hc12, hlam, hphi, p1057_1, u2elo3]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1016, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1057_1, u2elo3]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [hlam, p1057_0]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1016, h1053, hlam, hphi, ht01, ht0b, ht12, ht5b, p1057_1, u2elo3, u5ehi3]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1013, hlam, p1057_0]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h0, h1, h1013, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1057_1]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1053, hlam, p1057_0]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [h1054, hlam, p1057_1]
                    · have p1057_0 := h1057c.1
                      have p1057_1 := h1057c.2.1
                      have p1057_2 := h1057c.2.2.1
                      have p1057_3 := h1057c.2.2.2
                      linarith only [hlam, p1057_0]
                · linarith only [h1, h1013, h1020, h1054, hlam]
              · linarith only [h1, h1013, h1053, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1085 | h1085
      · linarith only [h0, h1, h1085, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1087 | h1087
        · linarith only [h0, h1085, h1087, h876, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1089 | h1089
          · linarith only [h1085, h1089, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1091 | h1091
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1092 | h1092
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1093 | h1093
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1094 | h1094
                  · linarith only [h0, h1013, h1089, h1094, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1013, h1094, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1097 | h1097
                  · linarith only [h0, h1013, h1097, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h1013, h1097, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1100 | h1100
                · linarith only [h1091, h1092, h1100, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1102 | h1102
                  · linarith only [h0, h1013, h1102, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h1013, h1102, hc12, hlam, hphi, u2elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1105 | h1105
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1106 | h1106
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1107 | h1107
                  · linarith only [h0, h1013, h1107, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h1013, h1107, hc12, hlam, hphi, u2elo4]
                · linarith only [h1091, h1105, h1106, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1111 | h1111
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1112 | h1112
                  · linarith only [h0, h1013, h1112, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h1013, h1112, hc12, hlam, hphi, u2elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1115 | h1115
                  · linarith only [h0, h1013, h1115, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h1013, h1115, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 3294000 in
set_option maxHeartbeats 3294000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_20_12_13_15_H_I_L_0_L_I_L_R_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

end R2N4
