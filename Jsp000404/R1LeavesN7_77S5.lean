import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_77S4

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_25_L_I_M_LI_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h328 | h328
  · rcases m.htr 0 3 5 (by decide) (by decide) with h329 | h329
    · rcases m.htr 2 3 5 (by decide) (by decide) with h330 | h330
      · rcases m.htr 2 4 5 (by decide) (by decide) with h331 | h331
        · rcases h5bigk with h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c | h332c
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [hlam, p332_0]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h0, hlam, p332_1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [hc25, hlam, hphi, p332_1, u5elo0]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h0, hc35, hlam, hphi, p332_1, u5elo1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p332_1, u5elo1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [hc05, hlam, hphi, p332_1, u5elo1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [hlam, p332_0]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h331, hc45, hlam, hphi, p332_1, u5elo1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [hc35, hlam, hphi, p332_1, u5elo1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [hc45, hlam, hphi, p332_1, u5elo1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h328, hlam, p332_1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [hc15, hlam, hphi, p332_1, u5elo2]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [hlam, p332_0]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h0, h328, hc35, hlam, hphi, p332_1, u5elo1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h0, h328, hc45, hlam, hphi, p332_1, u5elo1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h329, hlam, p332_1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h0, hc05, hlam, hphi, p332_1, u5elo3]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h330, hlam, p332_0]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [hlam, p332_0]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h0, h328, h330, hc45, hlam, hphi, p332_1, u5elo1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [hc05, hlam, hphi, p332_1, u5elo4]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h0, h328, h331, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p332_1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h331, hlam, p332_1]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [h328, h331, hc35, hlam, hphi, p332_1, u5elo0]
          · have p332_0 := h332c.1
            have p332_1 := h332c.2.1
            have p332_2 := h332c.2.2.1
            have p332_3 := h332c.2.2.2
            linarith only [hlam, p332_0]
        · rcases h5bigk with h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c | h358c
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [hlam, p358_0]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h0, hlam, p358_1]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h0, hc25, hlam, hphi, p358_1, u5elo1]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h0, hc35, hlam, hphi, p358_1, u5elo1]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p358_1, u5elo1]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [hc05, hlam, hphi, p358_1, u5elo1]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [hlam, p358_0]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h331, hc24, hlam, hphi, ht45, p358_1, u5elo1]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [hc35, hlam, hphi, p358_1, u5elo1]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h331, hc24, hlam, hphi, ht45, p358_1, u5elo1]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h328, hlam, p358_1]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [hc15, hlam, hphi, p358_1, u5elo2]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [hlam, p358_0]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h328, hc35, hlam, hphi, p358_1, u5elo0]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h331, hlam, p358_0]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h329, hlam, p358_1]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h0, hc05, hlam, hphi, p358_1, u5elo3]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h330, hlam, p358_0]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [hlam, p358_0]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h330, h331, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p358_1]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [hc05, hlam, hphi, p358_1, u5elo4]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [hc15, hlam, hphi, p358_1, u5elo4]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [h331, hc24, hlam, hphi, ht45, p358_1, u5elo4]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [hc35, hlam, hphi, p358_1, u5elo4]
          · have p358_0 := h358c.1
            have p358_1 := h358c.2.1
            have p358_2 := h358c.2.2.1
            have p358_3 := h358c.2.2.2
            linarith only [hlam, p358_0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h384 | h384
        · rcases h5bigk with h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [hlam, p385_0]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h0, hlam, p385_1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h330, hc23, hlam, hphi, ht34, ht45, p385_1, u5elo0]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h0, h330, hc23, hlam, hphi, ht34, ht45, p385_1, u5elo1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p385_1, u5elo1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [hc05, hlam, hphi, p385_1, u5elo1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [hlam, p385_0]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h330, hc23, hlam, hphi, ht34, ht45, p385_1, u5elo1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h330, hc23, hlam, hphi, ht34, ht45, p385_1, u5elo1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [hc45, hlam, hphi, p385_1, u5elo1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h328, hlam, p385_1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [hc15, hlam, hphi, p385_1, u5elo2]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [hlam, p385_0]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h330, hlam, p385_1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [hc45, hlam, hphi, p385_1, u5elo2]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h329, hlam, p385_1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h0, h329, hlam, p385_1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h0, h329, hc25, hlam, hphi, p385_1, u5elo1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [hlam, p385_0]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h0, h329, hc45, hlam, hphi, p385_1, u5elo1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [hc05, hlam, hphi, p385_1, u5elo4]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h384, hc15, hlam, hphi, p385_1, u5elo2]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h384, hlam, p385_1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [h330, h384, hlam, p385_1]
          · have p385_0 := h385c.1
            have p385_1 := h385c.2.1
            have p385_2 := h385c.2.2.1
            have p385_3 := h385c.2.2.2
            linarith only [hlam, p385_0]
        · rcases h5bigk with h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c | h411c
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [hlam, p411_0]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h0, hlam, p411_1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h0, hc25, hlam, hphi, p411_1, u5elo1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h0, hc35, hlam, hphi, p411_1, u5elo1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h0, h384, hc24, hlam, hphi, ht45, p411_1, u5elo1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [hc05, hlam, hphi, p411_1, u5elo1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [hlam, p411_0]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h330, hc23, hlam, hphi, ht34, ht45, p411_1, u5elo1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h330, hc23, hlam, hphi, ht34, ht45, p411_1, u5elo1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h384, hc24, hlam, hphi, ht45, p411_1, u5elo1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h328, hlam, p411_1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [hc15, hlam, hphi, p411_1, u5elo2]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [hlam, p411_0]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h330, hlam, p411_1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h384, hlam, p411_0]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h329, hlam, p411_1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h0, hc05, hlam, hphi, p411_1, u5elo3]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h329, hc25, hlam, hphi, p411_1, u5elo0]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [hlam, p411_0]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h0, h329, hc45, hlam, hphi, p411_1, u5elo1]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [hc05, hlam, hphi, p411_1, u5elo4]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [hc15, hlam, hphi, p411_1, u5elo4]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h330, hc23, hlam, hphi, ht34, ht45, p411_1, u5elo4]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [h330, hc23, hlam, hphi, ht34, ht45, p411_1, u5elo4]
          · have p411_0 := h411c.1
            have p411_1 := h411c.2.1
            have p411_2 := h411c.2.2.1
            have p411_3 := h411c.2.2.2
            linarith only [hlam, p411_0]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h437 | h437
      · linarith only [h328, h329, h437, hlam]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h439 | h439
        · rcases h5bigk with h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hlam, p440_0]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h0, hlam, p440_1]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h439, hc45, hlam, hphi, p440_1, u5elo0]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h329, hlam, p440_0]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h329, hc45, hlam, hphi, p440_1, u5elo3]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hc05, hlam, hphi, p440_1, u5elo1]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hlam, p440_0]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h437, hc23, hlam, hphi, ht34, ht45, p440_1, u5elo1]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hc35, hlam, hphi, p440_1, u5elo1]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hc45, hlam, hphi, p440_1, u5elo1]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h328, hlam, p440_1]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hc15, hlam, hphi, p440_1, u5elo2]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hlam, p440_0]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h437, hlam, p440_1]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h328, hc45, hlam, hphi, p440_1, u5elo0]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hc05, hlam, hphi, p440_1, u5elo3]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hc15, hlam, hphi, p440_1, u5elo3]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h437, hc23, hlam, hphi, ht34, ht45, p440_1, u5elo3]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hlam, p440_0]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hc45, hlam, hphi, p440_1, u5elo3]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h0, h439, hc01, hc24, hlam, hphi, ht12, p440_1]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h0, h439, hc01, hc25, hlam, hphi, ht12, p440_1]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h439, hlam, p440_1]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [h328, h439, hc35, hlam, hphi, p440_1, u5elo0]
          · have p440_0 := h440c.1
            have p440_1 := h440c.2.1
            have p440_2 := h440c.2.2.1
            have p440_3 := h440c.2.2.2
            linarith only [hlam, p440_0]
        · rcases h5bigk with h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c | h466c
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [hlam, p466_0]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h0, hlam, p466_1]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h439, hc24, hlam, hphi, ht45, p466_1, u5elo0]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h329, hlam, p466_0]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h0, hc45, hlam, hphi, p466_1, u5elo1]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [hc05, hlam, hphi, p466_1, u5elo1]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [hlam, p466_0]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h437, hc23, hlam, hphi, ht34, ht45, p466_1, u5elo1]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h329, hc03, hlam, hphi, ht34, ht45, p466_1, u5elo1]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h439, hc24, hlam, hphi, ht45, p466_1, u5elo1]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h328, hlam, p466_1]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [hc15, hlam, hphi, p466_1, u5elo2]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [hlam, p466_0]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h437, hlam, p466_1]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h439, hlam, p466_0]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [hc05, hlam, hphi, p466_1, u5elo3]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [hc15, hlam, hphi, p466_1, u5elo3]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h437, hc23, hlam, hphi, ht34, ht45, p466_1, u5elo3]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [hlam, p466_0]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h439, hc24, hlam, hphi, ht45, p466_1, u5elo3]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p466_1, u5elo4]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p466_1, u5elo4]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [h437, hc23, hlam, hphi, ht34, ht45, p466_1, u5elo4]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [hc35, hlam, hphi, p466_1, u5elo4]
          · have p466_0 := h466c.1
            have p466_1 := h466c.2.1
            have p466_2 := h466c.2.2.1
            have p466_3 := h466c.2.2.2
            linarith only [hlam, p466_0]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h492 | h492
    · rcases m.htr 2 3 5 (by decide) (by decide) with h493 | h493
      · rcases m.htr 2 4 5 (by decide) (by decide) with h494 | h494
        · rcases h5bigk with h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c | h495c
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hlam, p495_0]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [h0, hlam, p495_1]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [h328, hlam, p495_0]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hc35, hlam, hphi, p495_1, u5elo0]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hc45, hlam, hphi, p495_1, u5elo0]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hc05, hlam, hphi, p495_1, u5elo1]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hlam, p495_0]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hc25, hlam, hphi, p495_1, u5elo1]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hc35, hlam, hphi, p495_1, u5elo1]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hc45, hlam, hphi, p495_1, u5elo1]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p495_1, u5elo2]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hc15, hlam, hphi, p495_1, u5elo2]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hlam, p495_0]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hc35, hlam, hphi, p495_1, u5elo2]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hc45, hlam, hphi, p495_1, u5elo2]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [h492, hlam, p495_1]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [h0, h492, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p495_1]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [h493, hlam, p495_0]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hlam, p495_0]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [h492, hc45, hlam, hphi, p495_1, u5elo0]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hc05, hlam, hphi, p495_1, u5elo4]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [h0, h494, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p495_1, u5elo2]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [h494, hlam, p495_1]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [h494, hc35, hlam, hphi, p495_1, u5elo2]
          · have p495_0 := h495c.1
            have p495_1 := h495c.2.1
            have p495_2 := h495c.2.2.1
            have p495_3 := h495c.2.2.2
            linarith only [hlam, p495_0]
        · rcases h5bigk with h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hlam, p521_0]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h0, hlam, p521_1]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h328, hlam, p521_0]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hc35, hlam, hphi, p521_1, u5elo0]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h328, h494, hlam, p521_1]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hc05, hlam, hphi, p521_1, u5elo1]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hlam, p521_0]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hc25, hlam, hphi, p521_1, u5elo1]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hc35, hlam, hphi, p521_1, u5elo1]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h494, hc24, hlam, hphi, ht45, p521_1, u5elo1]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p521_1, u5elo2]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h494, hc15, hlam, hphi, p521_1, u5elo4]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hlam, p521_0]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h494, hc35, hlam, hphi, p521_1, u5elo4]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h494, hlam, p521_0]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h492, hlam, p521_1]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p521_1]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h493, hlam, p521_0]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hlam, p521_0]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h494, hc25, hlam, hphi, p521_1, u5elo3]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hc05, hlam, hphi, p521_1, u5elo4]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hc15, hlam, hphi, p521_1, u5elo4]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [h328, hc02, hlam, hphi, ht23, ht34, ht45, p521_1, u5elo4]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hc35, hlam, hphi, p521_1, u5elo4]
          · have p521_0 := h521c.1
            have p521_1 := h521c.2.1
            have p521_2 := h521c.2.2.1
            have p521_3 := h521c.2.2.2
            linarith only [hlam, p521_0]
      · linarith only [h328, h492, h493, hlam]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h548 | h548
      · rcases m.htr 2 4 5 (by decide) (by decide) with h549 | h549
        · rcases h5bigk with h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [hlam, p550_0]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h0, hlam, p550_1]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h328, hlam, p550_0]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h492, hlam, p550_0]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [hc45, hlam, hphi, p550_1, u5elo0]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [hc05, hlam, hphi, p550_1, u5elo1]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [hlam, p550_0]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h492, h548, hc03, hlam, hphi, ht34, ht45, p550_1, u5elo1]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h492, hc03, hlam, hphi, ht34, ht45, p550_1, u5elo1]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [hc45, hlam, hphi, p550_1, u5elo1]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p550_1, u5elo2]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [hc15, hlam, hphi, p550_1, u5elo2]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [hlam, p550_0]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h492, hc03, hlam, hphi, ht34, ht45, p550_1, u5elo2]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [hc45, hlam, hphi, p550_1, u5elo2]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h0, h548, hc01, hc23, hlam, hphi, ht12, p550_1]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h0, h548, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p550_1, u5elo2]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h548, hlam, p550_0]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [hlam, p550_0]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h548, hc45, hlam, hphi, p550_1, u5elo2]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p550_1, u5elo4]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h0, h549, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p550_1, u5elo2]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h549, hlam, p550_1]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [h549, hc35, hlam, hphi, p550_1, u5elo2]
          · have p550_0 := h550c.1
            have p550_1 := h550c.2.1
            have p550_2 := h550c.2.2.1
            have p550_3 := h550c.2.2.2
            linarith only [hlam, p550_0]
        · rcases h5bigk with h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [hlam, p576_0]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h0, hlam, p576_1]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h328, hlam, p576_0]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h492, hlam, p576_0]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h549, hc24, hlam, hphi, ht45, p576_1, u5elo0]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [hc05, hlam, hphi, p576_1, u5elo1]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [hlam, p576_0]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h328, hc02, hlam, hphi, ht23, ht34, ht45, p576_1, u5elo1]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h492, hc03, hlam, hphi, ht34, ht45, p576_1, u5elo1]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h328, h549, hc02, hlam, hphi, ht23, ht34, ht45, p576_1, u5elo1]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p576_1, u5elo2]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h549, hc15, hlam, hphi, p576_1, u5elo4]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [hlam, p576_0]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h492, h549, hc03, hlam, hphi, ht34, ht45, p576_1, u5elo4]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h549, hlam, p576_0]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p576_1, u5elo3]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h0, h548, h549, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p576_1, u5elo4]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h548, hlam, p576_0]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [hlam, p576_0]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h548, h549, hlam, p576_1]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p576_1, u5elo4]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p576_1, u5elo4]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [hc25, hlam, hphi, p576_1, u5elo4]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [h492, hc03, hlam, hphi, ht34, ht45, p576_1, u5elo4]
          · have p576_0 := h576c.1
            have p576_1 := h576c.2.1
            have p576_2 := h576c.2.2.1
            have p576_3 := h576c.2.2.2
            linarith only [hlam, p576_0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h602 | h602
        · rcases h5bigk with h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c | h603c
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [hlam, p603_0]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h0, hlam, p603_1]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h328, hlam, p603_0]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h492, hlam, p603_0]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [hc45, hlam, hphi, p603_1, u5elo0]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [hc05, hlam, hphi, p603_1, u5elo1]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [hlam, p603_0]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h328, hc02, hlam, hphi, ht23, ht34, ht45, p603_1, u5elo1]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h328, h548, hc02, hlam, hphi, ht23, ht34, ht45, p603_1, u5elo1]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [hc45, hlam, hphi, p603_1, u5elo1]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p603_1, u5elo2]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h548, hc15, hlam, hphi, p603_1, u5elo3]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [hlam, p603_0]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h548, hlam, p603_1]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h548, hc45, hlam, hphi, p603_1, u5elo3]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p603_1, u5elo3]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p603_1, u5elo3]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [hc25, hlam, hphi, p603_1, u5elo3]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [hlam, p603_0]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [hc45, hlam, hphi, p603_1, u5elo3]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p603_1, u5elo4]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h0, h602, hc01, hc24, hlam, hphi, ht12, p603_1]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h602, hlam, p603_1]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [h548, h602, hlam, p603_1]
          · have p603_0 := h603c.1
            have p603_1 := h603c.2.1
            have p603_2 := h603c.2.2.1
            have p603_3 := h603c.2.2.2
            linarith only [hlam, p603_0]
        · rcases h5bigk with h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c | h629c
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [hlam, p629_0]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h0, hlam, p629_1]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h328, hlam, p629_0]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h492, hlam, p629_0]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h602, hc24, hlam, hphi, ht45, p629_1, u5elo0]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [hc05, hlam, hphi, p629_1, u5elo1]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [hlam, p629_0]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h328, hc02, hlam, hphi, ht23, ht34, ht45, p629_1, u5elo1]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h548, hc23, hlam, hphi, ht34, ht45, p629_1, u5elo1]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h328, h602, hc02, hlam, hphi, ht23, ht34, ht45, p629_1, u5elo1]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p629_1, u5elo2]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h548, hc15, hlam, hphi, p629_1, u5elo3]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [hlam, p629_0]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h548, hlam, p629_1]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h602, hlam, p629_0]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p629_1, u5elo3]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p629_1, u5elo3]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [hc25, hlam, hphi, p629_1, u5elo3]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [hlam, p629_0]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h328, h602, hc02, hlam, hphi, ht23, ht34, ht45, p629_1, u5elo3]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p629_1, u5elo4]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p629_1, u5elo4]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [h328, hc02, hlam, hphi, ht23, ht34, ht45, p629_1, u5elo4]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [hc35, hlam, hphi, p629_1, u5elo4]
          · have p629_0 := h629c.1
            have p629_1 := h629c.2.1
            have p629_2 := h629c.2.2.1
            have p629_3 := h629c.2.2.2
            linarith only [hlam, p629_0]

theorem r1l7_12_25_L_I_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_12_25_L_I_M_LI_x0 m hb2 hb5 h0
  · exact r1l7_12_25_L_I_M_LI_x1 m hb2 hb5 h0

end R2N4
