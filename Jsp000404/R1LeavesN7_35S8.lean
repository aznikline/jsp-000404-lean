import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_35S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h865 | h865
  · rcases m.htr 1 2 3 (by decide) (by decide) with h866 | h866
    · rcases m.htr 1 2 4 (by decide) (by decide) with h867 | h867
      · rcases m.htr 1 2 5 (by decide) (by decide) with h868 | h868
        · rcases m.htr 1 3 4 (by decide) (by decide) with h869 | h869
          · linarith only [h0, h4, h865, h866, h869, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h871 | h871
            · linarith only [h0, h1, h4, h865, h871, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h873 | h873
              · linarith only [h0, h866, h873, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h875 | h875
                · linarith only [h0, h867, h875, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases h2bigk with h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c | h877c
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h0, h866, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p877_1]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    rcases p877_3 (m.d 0 2) (by simp) with h880 | h880
                    · rcases p877_3 (m.d 1 2) (by simp) with h881 | h881
                      · linarith only [h0, h881, hlam]
                      · linarith only [h866, h881, hlam]
                    · linarith only [h880, hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    rcases p877_3 (m.d 0 2) (by simp) with h885 | h885
                    · rcases p877_3 (m.d 1 2) (by simp) with h886 | h886
                      · linarith only [h0, h886, hlam]
                      · linarith only [h867, h886, hlam]
                    · linarith only [h885, hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p877_1, u5ehi2]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h0, hlam, p877_1]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p877_1]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h0, h871, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p877_1]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p877_1, u5ehi2]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h1, hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h866, hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h871, hlam, p877_1]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h873, hlam, p877_1]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h2, hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h867, hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h875, hc23, hc45, hlam, hphi, ht34, p877_1]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h875, hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h3, hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h868, hlam, p877_0]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p877_1]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [h0, h868, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p877_1]
                  · have p877_0 := h877c.1
                    have p877_1 := h877c.2.1
                    have p877_2 := h877c.2.2.1
                    have p877_3 := h877c.2.2.2
                    linarith only [hlam, p877_0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h911 | h911
          · linarith only [h3, h4, h865, h866, h868, h911, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h913 | h913
            · linarith only [h0, h1, h4, h865, h913, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h915 | h915
              · linarith only [h3, h865, h867, h868, h913, h915, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h917 | h917
                · linarith only [h0, h3, h867, h868, h917, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · linarith only [h4, h865, h867, h868, h913, h917, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h920 | h920
        · linarith only [h0, h2, h867, h920, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h922 | h922
          · linarith only [h4, h865, h866, h920, h922, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h924 | h924
            · linarith only [h1, h4, h924, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h926 | h926
              · linarith only [h3, h865, h866, h920, h926, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h928 | h928
                · rcases h2bigk with h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c | h929c
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [hlam, p929_0]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h0, h866, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p929_1]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    rcases p929_3 (m.d 0 2) (by simp) with h932 | h932
                    · rcases p929_3 (m.d 1 2) (by simp) with h933 | h933
                      · linarith only [h0, h933, hlam]
                      · linarith only [h866, h933, hlam]
                    · linarith only [h932, hlam, p929_0]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h0, h928, hc01, hlam, hphi, ht0b, ht5b, p929_1, u5ehi2]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p929_1, u5ehi2]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h0, hlam, p929_1]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [hlam, p929_0]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p929_1]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h867, hlam, p929_0]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h920, hlam, p929_0]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h1, hlam, p929_0]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h866, hlam, p929_0]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [hlam, p929_0]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h924, hlam, p929_1]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h926, hlam, p929_1]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h2, hlam, p929_0]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [hc12, hc24, hlam, hphi, p929_1]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p929_1]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [hlam, p929_0]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h0, h2, h866, h920, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p929_1]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h3, hlam, p929_0]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h866, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p929_1]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p929_1]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [h928, hlam, p929_1]
                  · have p929_0 := h929c.1
                    have p929_1 := h929c.2.1
                    have p929_2 := h929c.2.2.1
                    have p929_3 := h929c.2.2.2
                    linarith only [hlam, p929_0]
                · linarith only [h4, h865, h866, h867, h928, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h960 | h960
      · rcases m.htr 1 2 5 (by decide) (by decide) with h961 | h961
        · linarith only [h1, h4, h866, h961, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h963 | h963
          · linarith only [h1, h4, h866, h960, h963, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h866, h960, h963, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h966 | h966
        · linarith only [h1, h4, h866, h966, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h968 | h968
          · linarith only [h1, h4, h866, h968, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h970 | h970
            · linarith only [h1, h4, h970, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h972 | h972
              · rcases m.htr 2 4 5 (by decide) (by decide) with h973 | h973
                · rcases h2bigk with h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [hlam, p974_0]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    rcases p974_3 (m.d 0 2) (by simp) with h976 | h976
                    · rcases p974_3 (m.d 1 2) (by simp) with h977 | h977
                      · linarith only [h0, h977, hlam]
                      · rcases p974_3 (m.d 2 3) (by simp) with h979 | h979
                        · linarith only [h1, h979, hlam]
                        · linarith only [h866, h979, hlam]
                    · linarith only [h0, h976, hlam]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h0, h972, hc01, hlam, hphi, ht0b, ht5b, p974_1, u5ehi3]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h0, h970, h972, hc01, hlam, hphi, ht0b, ht5b, p974_1, u5ehi3]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h0, h966, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p974_1]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h0, hlam, p974_1]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [hlam, p974_0]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h866, hlam, p974_0]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h960, hlam, p974_0]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h966, hlam, p974_0]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h1, hlam, p974_0]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p974_1]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [hlam, p974_0]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h970, hlam, p974_1]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h1, h4, h966, hc12, hc34, hlam, hphi, ht23, p974_1]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h2, hlam, p974_0]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h0, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p974_1]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p974_1]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [hlam, p974_0]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h0, h2, h966, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p974_1]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h3, hlam, p974_0]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p974_1]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h972, hlam, p974_0]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [h973, hlam, p974_1]
                  · have p974_0 := h974c.1
                    have p974_1 := h974c.2.1
                    have p974_2 := h974c.2.2.1
                    have p974_3 := h974c.2.2.2
                    linarith only [hlam, p974_0]
                · linarith only [h4, h865, h960, h973, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1007 | h1007
                · rcases h2bigk with h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [hlam, p1008_0]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    rcases p1008_3 (m.d 0 2) (by simp) with h1010 | h1010
                    · rcases p1008_3 (m.d 1 2) (by simp) with h1011 | h1011
                      · linarith only [h0, h1011, hlam]
                      · rcases p1008_3 (m.d 2 3) (by simp) with h1013 | h1013
                        · linarith only [h1, h1013, hlam]
                        · linarith only [h1013, h866, hlam]
                    · linarith only [h0, h1010, hlam]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h0, h866, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1008_1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h0, h1007, hc01, hlam, hphi, ht0b, ht5b, p1008_1, u5ehi4]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h0, h966, hc01, hlam, hphi, ht0b, ht5b, p1008_1, u5ehi1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h0, hlam, p1008_1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [hlam, p1008_0]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h866, hlam, p1008_0]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h960, hlam, p1008_0]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h966, hlam, p1008_0]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h1, hlam, p1008_0]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p1008_1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [hlam, p1008_0]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h970, hlam, p1008_1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h972, hlam, p1008_1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h2, hlam, p1008_0]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [hc12, hc24, hlam, hphi, p1008_1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1008_1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [hlam, p1008_0]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h0, h2, h866, h972, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1008_1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h3, hlam, p1008_0]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p1008_1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h0, h3, h866, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1008_1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [h1007, hlam, p1008_1]
                  · have p1008_0 := h1008c.1
                    have p1008_1 := h1008c.2.1
                    have p1008_2 := h1008c.2.2.1
                    have p1008_3 := h1008c.2.2.2
                    linarith only [hlam, p1008_0]
                · linarith only [h1007, h4, h865, h960, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1041 | h1041
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1042 | h1042
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1043 | h1043
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1044 | h1044
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1045 | h1045
            · linarith only [h1, h1045, h4, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1047 | h1047
              · linarith only [h0, h1, h1041, h1044, h1047, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1049 | h1049
                · linarith only [h0, h1041, h1044, h1049, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases h2bigk with h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c | h1051c
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h0, h1041, h1044, h4, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1051_1]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    rcases p1051_3 (m.d 0 2) (by simp) with h1054 | h1054
                    · rcases p1051_3 (m.d 1 2) (by simp) with h1055 | h1055
                      · linarith only [h0, h1055, hlam]
                      · linarith only [h1041, h1055, hlam]
                    · linarith only [h1054, hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    rcases p1051_3 (m.d 0 2) (by simp) with h1059 | h1059
                    · rcases p1051_3 (m.d 1 2) (by simp) with h1060 | h1060
                      · linarith only [h0, h1060, hlam]
                      · linarith only [h1042, h1060, hlam]
                    · linarith only [h1059, hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1051_1, u5ehi2]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h0, hlam, p1051_1]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1051_1]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1051_1]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1051_1, u5ehi2]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h1, hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h1041, hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h1045, hlam, p1051_1]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h1047, hlam, p1051_1]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h2, hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h1042, hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1051_1]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h1049, hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h3, hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h1043, hlam, p1051_0]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1051_1]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [h0, h1043, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1051_1]
                  · have p1051_0 := h1051c.1
                    have p1051_1 := h1051c.2.1
                    have p1051_2 := h1051c.2.2.1
                    have p1051_3 := h1051c.2.2.2
                    linarith only [hlam, p1051_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1085 | h1085
            · linarith only [h1, h1085, h4, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1087 | h1087
              · linarith only [h0, h1041, h1087, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1089 | h1089
                · linarith only [h0, h1042, h1089, h865, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases h2bigk with h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, h1043, hc01, hlam, hphi, ht0b, ht5b, p1091_1, u5ehi2]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    rcases p1091_3 (m.d 0 2) (by simp) with h1094 | h1094
                    · rcases p1091_3 (m.d 1 2) (by simp) with h1095 | h1095
                      · linarith only [h0, h1095, hlam]
                      · linarith only [h1041, h1095, hlam]
                    · linarith only [h1094, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    rcases p1091_3 (m.d 0 2) (by simp) with h1099 | h1099
                    · rcases p1091_3 (m.d 1 2) (by simp) with h1100 | h1100
                      · linarith only [h0, h1100, hlam]
                      · linarith only [h1042, h1100, hlam]
                    · linarith only [h1099, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1091_1, u5ehi2]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, hlam, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1091_1, u5ehi2]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1041, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1085, hlam, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1087, hlam, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h2, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1042, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1089, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h3, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1043, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, h1043, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [hlam, p1091_0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1125 | h1125
          · linarith only [h0, h1041, h1043, h1125, h3, h4, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1127 | h1127
            · linarith only [h1, h1127, h4, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1129 | h1129
              · linarith only [h0, h1042, h1043, h1127, h1129, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1131 | h1131
                · linarith only [h1042, h1043, h1131, h3, h865, hlam]
                · rcases h2bigk with h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c | h1133c
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h0, h1042, h1127, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1133_1]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    rcases p1133_3 (m.d 0 2) (by simp) with h1136 | h1136
                    · rcases p1133_3 (m.d 1 2) (by simp) with h1137 | h1137
                      · linarith only [h0, h1137, hlam]
                      · linarith only [h1041, h1137, hlam]
                    · linarith only [h1136, hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    rcases p1133_3 (m.d 0 2) (by simp) with h1141 | h1141
                    · rcases p1133_3 (m.d 1 2) (by simp) with h1142 | h1142
                      · linarith only [h0, h1142, hlam]
                      · linarith only [h1042, h1142, hlam]
                    · linarith only [h1141, hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1133_1, u5ehi2]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h0, hlam, p1133_1]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1133_1]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h0, h1127, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1133_1]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h1043, hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h1, hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h1041, hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h1127, hlam, p1133_1]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h1129, hlam, p1133_1]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h2, hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h1042, hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1133_1]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h1131, hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h3, hlam, p1133_0]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p1133_1]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1133_1]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [h0, h1127, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1133_1]
                  · have p1133_0 := h1133c.1
                    have p1133_1 := h1133c.2.1
                    have p1133_2 := h1133c.2.2.1
                    have p1133_3 := h1133c.2.2.2
                    linarith only [hlam, p1133_0]
      · linarith only [h1041, h1042, h2, h865, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1168 | h1168
      · linarith only [h1, h1041, h1168, h4, h865, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1170 | h1170
        · linarith only [h1, h1041, h1170, h4, h865, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1172 | h1172
          · linarith only [h1, h1041, h1172, h4, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1174 | h1174
            · linarith only [h1, h1174, h4, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1176 | h1176
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1177 | h1177
                · linarith only [h1, h1176, h1177, h4, h865, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h1174, h1176, h1177, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1180 | h1180
                · linarith only [h1, h1041, h1180, h4, h865, hc12, hc24, hlam, hphi]
                · rcases h2bigk with h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c | h1182c
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [hlam, p1182_0]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    rcases p1182_3 (m.d 0 2) (by simp) with h1184 | h1184
                    · rcases p1182_3 (m.d 1 2) (by simp) with h1185 | h1185
                      · linarith only [h0, h1185, hlam]
                      · rcases p1182_3 (m.d 2 3) (by simp) with h1187 | h1187
                        · linarith only [h1, h1187, hlam]
                        · linarith only [h1041, h1187, hlam]
                    · linarith only [h0, h1184, hlam]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h0, h1041, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1182_1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h0, h1168, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1182_1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h0, h1170, hc01, hlam, hphi, ht0b, ht5b, p1182_1, u5ehi1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h0, hlam, p1182_1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [hlam, p1182_0]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h1041, hlam, p1182_0]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h1168, hlam, p1182_0]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h1170, hlam, p1182_0]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h1, hlam, p1182_0]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [hc12, hc23, hlam, hphi, p1182_1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [hlam, p1182_0]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h1174, hlam, p1182_1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h1176, hlam, p1182_1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h2, hlam, p1182_0]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [hc12, hc24, hlam, hphi, p1182_1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h2, h865, hc23, hc45, hlam, hphi, ht34, p1182_1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [hlam, p1182_0]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h1180, hlam, p1182_0]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h3, hlam, p1182_0]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [hc12, hc25, hlam, hphi, p1182_1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h0, h1041, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1182_1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [h0, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1182_1]
                  · have p1182_0 := h1182c.1
                    have p1182_1 := h1182c.2.1
                    have p1182_2 := h1182c.2.2.1
                    have p1182_3 := h1182c.2.2.2
                    linarith only [hlam, p1182_0]

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_22_15_H_I_L_R_x0_x0_x0_x0_x0 m hb2 hb5 h0 h1 h2 h3 h4
  · exact r1l7_22_15_H_I_L_R_x0_x0_x0_x0_x1 m hb2 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1214 | h1214
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1215 | h1215
    · linarith only [h1, h1214, h1215, h3, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1217 | h1217
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1218 | h1218
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1219 | h1219
          · linarith only [h0, h1219, h3, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1221 | h1221
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1222 | h1222
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1223 | h1223
                · linarith only [h0, h1217, h1223, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1225 | h1225
                  · linarith only [h1215, h1223, h1225, h2, h3, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1217, h1222, h1225, h3, hc34, hc45, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1228 | h1228
                · linarith only [h0, h1217, h1221, h1222, h1228, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h0, h1217, h1221, h1222, h1228, h3, hc23, hc35, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1231 | h1231
              · linarith only [h1217, h1221, h1231, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1233 | h1233
                · linarith only [h1214, h1217, h1221, h1233, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                · linarith only [h1, h1214, h1221, h1233, h3, hc13, hc35, hlam, hphi]
        · linarith only [h1218, h2, h3, hc12, hc25, hlam, hphi]
      · linarith only [h1, h1217, h3, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1238 | h1238
    · linarith only [h1238, h2, h3, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1240 | h1240
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1241 | h1241
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1242 | h1242
          · linarith only [h0, h1242, h3, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1244 | h1244
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1245 | h1245
              · linarith only [h1, h1214, h1245, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1247 | h1247
                · linarith only [h0, h1, h1214, h1240, h1244, h1247, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h0, h1214, h1240, h1244, h1247, h3, hc03, hc35, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1250 | h1250
              · linarith only [h1, h1244, h1250, h3, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1252 | h1252
                · linarith only [h0, h1241, h1250, h1252, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1254 | h1254
                  · linarith only [h0, h1238, h1241, h1252, h1254, h3, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases h2bigk with h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [hlam, p1256_0]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1254, h3, hc12, hc45, hlam, hphi, ht23, ht34, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1254, h3, hc23, hc45, hlam, hphi, ht34, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1250, h1254, h3, hc23, hc45, hlam, hphi, ht34, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h3, hlam, p1256_0]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h0, hlam, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [hlam, p1256_0]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h0, h1250, h1254, h3, hc23, hc45, hlam, hphi, ht34, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1242, hlam, p1256_0]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1, hlam, p1256_0]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1240, hlam, p1256_0]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [hlam, p1256_0]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1250, hlam, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1252, hlam, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h2, hlam, p1256_0]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1241, hlam, p1256_0]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1254, h2, h3, hc23, hc45, hlam, hphi, ht34, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [hlam, p1256_0]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1254, hlam, p1256_0]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1254, hc02, hc45, hlam, hphi, ht23, ht34, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1254, hc12, hc45, hlam, hphi, ht23, ht34, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1254, hc23, hc45, hlam, hphi, ht34, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [h1250, h1254, hc23, hc45, hlam, hphi, ht34, p1256_1]
                    · have p1256_0 := h1256c.1
                      have p1256_1 := h1256c.2.1
                      have p1256_2 := h1256c.2.2.1
                      have p1256_3 := h1256c.2.2.2
                      linarith only [hlam, p1256_0]
        · linarith only [h1241, h2, h3, hc12, hc25, hlam, hphi]
      · linarith only [h1, h1240, h3, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_22_15_H_I_L_R_x0_x0_x0_x0 m hb2 hb5 h0 h1 h2 h3
  · exact r1l7_22_15_H_I_L_R_x0_x0_x0_x1 m hb2 hb5 h0 h1 h2 h3

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1284 | h1284
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1285 | h1285
    · linarith only [h1, h1285, h2, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1287 | h1287
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1288 | h1288
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1289 | h1289
          · linarith only [h0, h1289, h2, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1291 | h1291
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1292 | h1292
              · linarith only [h0, h1285, h1288, h1292, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1294 | h1294
                · linarith only [h1, h1292, h1294, h2, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1296 | h1296
                  · linarith only [h0, h1288, h1296, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1298 | h1298
                    · rcases h2bigk with h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c | h1299c
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [hlam, p1299_0]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1294, h2, hc12, hc34, hlam, hphi, ht23, p1299_1]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1294, h2, hc23, hc34, hlam, hphi, p1299_1]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h2, hlam, p1299_0]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1294, h1298, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1299_1, u5ehi4]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h0, hlam, p1299_1]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [hlam, p1299_0]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1299_1]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1289, hlam, p1299_0]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h0, h1294, h1298, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1299_1, u5ehi4]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1, hlam, p1299_0]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1288, hlam, p1299_0]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [hlam, p1299_0]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1294, hlam, p1299_1]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1296, hlam, p1299_1]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1294, hc02, hc34, hlam, hphi, ht23, p1299_1]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1294, hc12, hc34, hlam, hphi, ht23, p1299_1]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1294, hc23, hc34, hlam, hphi, p1299_1]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [hlam, p1299_0]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1294, h1298, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1299_1, u5ehi4]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1284, hlam, p1299_0]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1291, hlam, p1299_0]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h0, h1291, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1299_1]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [h1298, hlam, p1299_1]
                      · have p1299_0 := h1299c.1
                        have p1299_1 := h1299c.2.1
                        have p1299_2 := h1299c.2.2.1
                        have p1299_3 := h1299c.2.2.2
                        linarith only [hlam, p1299_0]
                    · linarith only [h0, h1287, h1291, h1298, h2, hc05, hlam, hphi, ht0b, ht5b, u5ehi2]
            · linarith only [h1284, h1291, h2, hc12, hc24, hlam, hphi]
        · linarith only [h1, h1288, h2, hc12, hc24, hlam, hphi]
      · linarith only [h1284, h1287, h2, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1329 | h1329
    · linarith only [h1, h1329, h2, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1331 | h1331
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1332 | h1332
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1333 | h1333
          · linarith only [h0, h1333, h2, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1335 | h1335
            · linarith only [h0, h1284, h1335, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1337 | h1337
              · linarith only [h0, h1284, h1329, h1331, h1332, h1337, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1339 | h1339
                · linarith only [h1, h1329, h1339, h2, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1341 | h1341
                  · linarith only [h0, h1332, h1341, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1343 | h1343
                    · rcases h2bigk with h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [hlam, p1344_0]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1284, h1339, h1343, hc12, hc34, hlam, hphi, ht23, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1284, h1339, h1343, hc23, hc34, hlam, hphi, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h2, hlam, p1344_0]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1284, hlam, p1344_0]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h0, hlam, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [hlam, p1344_0]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1333, hlam, p1344_0]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1335, hlam, p1344_0]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1, hlam, p1344_0]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1332, hlam, p1344_0]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [hlam, p1344_0]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1339, hlam, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1341, hlam, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1339, hc02, hc34, hlam, hphi, ht23, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1332, h1339, hc23, hc34, hlam, hphi, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1339, hc23, hc34, hlam, hphi, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [hlam, p1344_0]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1339, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1344_1, u5ehi2]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h0, h1332, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1332, h1341, hc23, hc35, hlam, hphi, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1341, hc23, hc35, hlam, hphi, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [h1343, hlam, p1344_1]
                      · have p1344_0 := h1344c.1
                        have p1344_1 := h1344c.2.1
                        have p1344_2 := h1344c.2.2.1
                        have p1344_3 := h1344c.2.2.2
                        linarith only [hlam, p1344_0]
                    · linarith only [h0, h1331, h1332, h1343, h2, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h1, h1332, h2, hc12, hc24, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1372 | h1372
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1373 | h1373
          · linarith only [h0, h1373, h2, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1375 | h1375
            · linarith only [h0, h1284, h1375, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1377 | h1377
              · linarith only [h0, h1, h1329, h1331, h1372, h1377, h2, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1379 | h1379
                · linarith only [h1, h1331, h1377, h1379, h2, hc13, hc45, hlam, hphi, ht34]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1381 | h1381
                  · linarith only [h0, h1331, h1372, h1381, h2, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1383 | h1383
                    · linarith only [h0, h1331, h1372, h1379, h1383, h2, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1372, h1383, h2, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h1, h1372, h2, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 7820000 in
set_option maxHeartbeats 7820000 in
theorem r1l7_22_15_H_I_L_R_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_22_15_H_I_L_R_x0_x0_x0 m hb2 hb5 h0 h1 h2
  · exact r1l7_22_15_H_I_L_R_x0_x0_x1 m hb2 hb5 h0 h1 h2

end R2N4
