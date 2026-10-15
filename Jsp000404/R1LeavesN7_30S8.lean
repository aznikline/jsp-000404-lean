import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3236 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h3237 | h3237
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3238 | h3238
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3239 | h3239
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3240 | h3240
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3241 | h3241
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3242 | h3242
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3243 | h3243
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3244 | h3244
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3245 | h3245
                  · rcases h0bigk with h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c | h3246c
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [hlam, p3246_0]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h0, hlam, p3246_1]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h2474, hlam, p3246_0]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h3243, hc01, hlam, hphi, ht0b, ht5b, p3246_1, u5ehi4]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h2474, hc13, hlam, hphi, ht01, ht0b, ht5b, p3246_1, u5ehi0]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p3246_1]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [hlam, p3246_0]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h0, h3242, hc12, hlam, hphi, ht01, ht0b, ht5b, p3246_1, u5ehi3]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h0, h3243, hc12, hlam, hphi, ht01, ht0b, ht5b, p3246_1, u5ehi4]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h0, h3237, hc12, hlam, hphi, ht01, ht0b, ht5b, p3246_1, u5ehi1]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h3236, h3243, hc03, hlam, hphi, ht0b, ht5b, p3246_1, u5ehi4]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h3238, hlam, p3246_1]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [hlam, p3246_0]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h0, h3238, h3243, hc12, hlam, hphi, ht01, ht0b, ht5b, p3246_1, u5ehi4]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h0, h3237, h3238, hc12, hlam, hphi, ht01, ht0b, ht5b, p3246_1, u5ehi1]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h3236, hlam, p3246_0]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h3239, hlam, p3246_0]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h3241, hlam, p3246_0]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [hlam, p3246_0]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h3236, h3237, hc01, hlam, hphi, ht0b, ht5b, p3246_1, u5ehi1]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h3237, hlam, p3246_0]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h3240, hlam, p3246_1]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h3242, hlam, p3246_0]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [h3243, hlam, p3246_1]
                    · have p3246_0 := h3246c.1
                      have p3246_1 := h3246c.2.1
                      have p3246_2 := h3246c.2.2.1
                      have p3246_3 := h3246c.2.2.2
                      linarith only [hlam, p3246_0]
                  · rcases h0bigk with h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c | h3272c
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [hlam, p3272_0]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h0, hlam, p3272_1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h2474, hlam, p3272_0]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h2474, h3244, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3272_1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h2474, h3237, h3244, hc12, hlam, hphi, ht01, ht0b, ht5b, p3272_1, u5ehi1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p3272_1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [hlam, p3272_0]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h0, h2474, hc01, hc12, hlam, hphi, p3272_1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h0, h3241, h3245, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3272_1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h0, h3237, hc12, hlam, hphi, ht01, ht0b, ht5b, p3272_1, u5ehi1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h3237, hc03, hlam, hphi, ht0b, ht5b, p3272_1, u5ehi1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h3238, hlam, p3272_1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [hlam, p3272_0]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h2474, h3241, h3244, h3245, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3272_1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h2474, h3237, h3244, hc12, hlam, hphi, ht01, ht0b, ht5b, p3272_1, u5ehi1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h3236, hlam, p3272_0]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h3239, hlam, p3272_0]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h3241, hlam, p3272_0]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [hlam, p3272_0]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h3236, h3237, hc01, hlam, hphi, ht0b, ht5b, p3272_1, u5ehi1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h3237, hlam, p3272_0]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h3240, hlam, p3272_1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h3242, hlam, p3272_0]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [h3243, hlam, p3272_1]
                    · have p3272_0 := h3272c.1
                      have p3272_1 := h3272c.2.1
                      have p3272_2 := h3272c.2.2.1
                      have p3272_3 := h3272c.2.2.2
                      linarith only [hlam, p3272_0]
                · linarith only [h0, h3237, h3244, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3299 | h3299
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3300 | h3300
                  · rcases h0bigk with h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c | h3301c
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [hlam, p3301_0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h0, hlam, p3301_1]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h2474, hlam, p3301_0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h2474, h3299, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3301_1]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [hc01, hlam, hphi, ht0b, ht5b, p3301_1, u5ehi0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p3301_1]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [hlam, p3301_0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h0, h2474, hc01, hc12, hlam, hphi, p3301_1]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      rcases p3301_3 (m.d 0 1) (by simp) with h3310 | h3310
                      · linarith only [h0, h3310, hlam]
                      · linarith only [h3236, h3310, hlam]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h0, h3237, hc12, hlam, hphi, ht01, ht0b, ht5b, p3301_1, u5ehi1]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h3237, hc03, hlam, hphi, ht0b, ht5b, p3301_1, u5ehi1]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h3238, hlam, p3301_1]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [hlam, p3301_0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      rcases p3301_3 (m.d 0 1) (by simp) with h3317 | h3317
                      · linarith only [h2474, h3317, hlam]
                      · linarith only [h3236, h3317, hlam]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h2474, h3237, h3299, hc12, hlam, hphi, ht01, ht0b, ht5b, p3301_1, u5ehi1]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h3236, hlam, p3301_0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h3239, hlam, p3301_0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h3241, hlam, p3301_0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [hlam, p3301_0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h3243, hlam, p3301_0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h3237, hlam, p3301_0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h3240, hlam, p3301_1]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h3242, hlam, p3301_0]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [h0, h3237, h3239, h3300, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3301_1]
                    · have p3301_0 := h3301c.1
                      have p3301_1 := h3301c.2.1
                      have p3301_2 := h3301c.2.2.1
                      have p3301_3 := h3301c.2.2.2
                      linarith only [hlam, p3301_0]
                  · rcases h0bigk with h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c | h3331c
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [hlam, p3331_0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h0, hlam, p3331_1]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h2474, hlam, p3331_0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h2474, h3299, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3331_1]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h2474, h3299, hc12, hlam, hphi, ht01, ht0b, ht5b, p3331_1, u5ehi0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p3331_1]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [hlam, p3331_0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h0, h2474, h3237, hc12, hlam, hphi, ht01, ht0b, ht5b, p3331_1, u5ehi1]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h0, h3241, h3300, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3331_1]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h0, h3240, hc12, hlam, hphi, ht01, ht0b, ht5b, p3331_1, u5ehi2]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h3237, hc03, hlam, hphi, ht0b, ht5b, p3331_1, u5ehi1]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h3238, hlam, p3331_1]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [hlam, p3331_0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h2474, h3241, h3299, h3300, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3331_1]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h2474, h3240, h3299, hc12, hlam, hphi, ht01, ht0b, ht5b, p3331_1, u5ehi2]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h3236, hlam, p3331_0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h3239, hlam, p3331_0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h3241, hlam, p3331_0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [hlam, p3331_0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h3243, hlam, p3331_0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h3237, hlam, p3331_0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h3240, hlam, p3331_1]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h3242, hlam, p3331_0]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [h3241, h3300, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3331_1]
                    · have p3331_0 := h3331c.1
                      have p3331_1 := h3331c.2.1
                      have p3331_2 := h3331c.2.2.1
                      have p3331_3 := h3331c.2.2.2
                      linarith only [hlam, p3331_0]
                · linarith only [h0, h3237, h3299, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h2474, h3237, h3242, hlam]
          · linarith only [h2474, h3236, h3241, hlam]
        · linarith only [h0, h3237, h3240, hlam]
      · linarith only [h2474, h3236, h3238, h3239, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3362 | h3362
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3363 | h3363
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3364 | h3364
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3365 | h3365
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3366 | h3366
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3367 | h3367
                · linarith only [h3238, h3363, h3367, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h3236, h3366, h3367, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3370 | h3370
                · linarith only [h0, h3237, h3238, h3370, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h3237, h3370, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h3237, h3238, h3365, hlam]
          · linarith only [h0, h3236, h3238, h3364, hlam]
        · linarith only [h0, h3237, h3363, hlam]
      · linarith only [h0, h3236, h3362, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h3377 | h3377
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3378 | h3378
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3379 | h3379
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3380 | h3380
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3381 | h3381
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3382 | h3382
              · linarith only [h3236, h3237, h3382, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3384 | h3384
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3385 | h3385
                  · rcases h0bigk with h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c | h3386c
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [hlam, p3386_0]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h0, hlam, p3386_1]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h2474, hlam, p3386_0]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h2474, h3384, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3386_1]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h3237, hlam, p3386_1]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p3386_1]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [hlam, p3386_0]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h0, h3381, hc12, hlam, hphi, ht01, ht0b, ht5b, p3386_1, u5ehi3]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      rcases p3386_3 (m.d 0 1) (by simp) with h3395 | h3395
                      · linarith only [h0, h3395, hlam]
                      · linarith only [h3236, h3395, hlam]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h0, h3236, h3237, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3386_1]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h3236, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p3386_1]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h3377, hlam, p3386_1]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [hlam, p3386_0]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      rcases p3386_3 (m.d 0 1) (by simp) with h3402 | h3402
                      · linarith only [h2474, h3402, hlam]
                      · linarith only [h3236, h3402, hlam]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h0, h3236, h3237, h3377, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3386_1]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h3236, hlam, p3386_0]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h3378, hlam, p3386_0]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h3380, hlam, p3386_0]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [hlam, p3386_0]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h3382, hlam, p3386_0]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h3236, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p3386_1]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h3379, hlam, p3386_1]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h3381, hlam, p3386_0]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [h3378, h3382, h3385, hc34, hc45, hlam, hphi, p3386_1]
                    · have p3386_0 := h3386c.1
                      have p3386_1 := h3386c.2.1
                      have p3386_2 := h3386c.2.2.1
                      have p3386_3 := h3386c.2.2.2
                      linarith only [hlam, p3386_0]
                  · rcases h0bigk with h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c | h3416c
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [hlam, p3416_0]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h0, hlam, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h2474, hlam, p3416_0]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h3237, hlam, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [hlam, p3416_0]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h0, h2474, hc01, hc12, hlam, hphi, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h0, h3380, h3385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3416_1, u5ehi0]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h3236, h3380, h3385, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h3377, hlam, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [hlam, p3416_0]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h2474, h3380, h3384, h3385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h2474, h3236, h3237, h3380, h3384, h3385, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h3236, hlam, p3416_0]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h3378, hlam, p3416_0]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h3380, hlam, p3416_0]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [hlam, p3416_0]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h3382, hlam, p3416_0]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h3236, h3380, h3385, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h3379, hlam, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h3381, hlam, p3416_0]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [h3380, h3382, h3385, hc23, hc45, hlam, hphi, ht34, p3416_1]
                    · have p3416_0 := h3416c.1
                      have p3416_1 := h3416c.2.1
                      have p3416_2 := h3416c.2.2.1
                      have p3416_3 := h3416c.2.2.2
                      linarith only [hlam, p3416_0]
                · linarith only [h0, h3377, h3384, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3443 | h3443
              · linarith only [h3236, h3237, h3443, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3445 | h3445
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3446 | h3446
                  · rcases h0bigk with h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c | h3447c
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [hlam, p3447_0]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h0, hlam, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h2474, hlam, p3447_0]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h2474, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3237, hlam, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [hlam, p3447_0]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h0, h2474, h3236, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      rcases p3447_3 (m.d 0 1) (by simp) with h3456 | h3456
                      · linarith only [h0, h3456, hlam]
                      · linarith only [h3236, h3456, hlam]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3447_1, u5ehi0]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3236, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3377, hlam, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [hlam, p3447_0]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3378, h3381, h3443, h3446, hc34, hc45, hlam, hphi, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3381, hlam, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3236, hlam, p3447_0]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3378, hlam, p3447_0]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3380, hlam, p3447_0]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [hlam, p3447_0]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3443, hlam, p3447_0]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3236, h3443, hc14, hc45, hlam, hphi, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3379, hlam, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3443, hc03, hc45, hlam, hphi, ht34, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [h3378, h3443, h3446, hc34, hc45, hlam, hphi, p3447_1]
                    · have p3447_0 := h3447c.1
                      have p3447_1 := h3447c.2.1
                      have p3447_2 := h3447c.2.2.1
                      have p3447_3 := h3447c.2.2.2
                      linarith only [hlam, p3447_0]
                  · linarith only [h3380, h3381, h3446, hc23, hc35, hlam, hphi]
                · linarith only [h0, h3377, h3445, hlam]
          · linarith only [h2474, h3236, h3380, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3478 | h3478
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3479 | h3479
            · linarith only [h3377, h3379, h3479, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3481 | h3481
              · linarith only [h0, h3236, h3379, h3481, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3483 | h3483
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3484 | h3484
                  · rcases h0bigk with h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [hlam, p3485_0]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h0, hlam, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h2474, hlam, p3485_0]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h2474, h3377, h3379, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3237, hlam, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3379, hc01, hc25, hlam, hphi, ht12, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [hlam, p3485_0]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3379, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3236, h3379, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3379, hlam, p3485_0]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3236, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3377, hlam, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [hlam, p3485_0]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3236, h3479, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3479, hlam, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3236, hlam, p3485_0]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3378, hlam, p3485_0]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3478, hlam, p3485_0]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [hlam, p3485_0]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3481, hlam, p3485_0]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3236, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3379, hc02, hc25, hlam, hphi, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3479, hc03, hc35, hlam, hphi, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [h3236, h3481, hc14, hc45, hlam, hphi, p3485_1]
                    · have p3485_0 := h3485c.1
                      have p3485_1 := h3485c.2.1
                      have p3485_2 := h3485c.2.2.1
                      have p3485_3 := h3485c.2.2.2
                      linarith only [hlam, p3485_0]
                  · linarith only [h3478, h3479, h3484, hc23, hc35, hlam, hphi]
                · linarith only [h0, h3377, h3483, hlam]
          · linarith only [h2474, h3236, h3478, hlam]
      · linarith only [h0, h3236, h3378, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3515 | h3515
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3516 | h3516
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3517 | h3517
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3518 | h3518
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3519 | h3519
              · linarith only [h3236, h3237, h3519, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3521 | h3521
                · linarith only [h3377, h3516, h3521, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3523 | h3523
                  · rcases h0bigk with h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c | h3524c
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [hlam, p3524_0]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h0, hlam, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h2474, hlam, p3524_0]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h0, h3515, h3521, h3523, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h3237, hlam, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h0, h3521, hc01, hc23, hlam, hphi, ht12, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [hlam, p3524_0]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h3377, hlam, p3524_0]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h0, h3515, h3521, h3523, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h0, h3236, h3237, h3521, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h3236, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h2474, h3521, hc02, hc23, hlam, hphi, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [hlam, p3524_0]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      rcases p3524_3 (m.d 0 1) (by simp) with h3538 | h3538
                      · linarith only [h2474, h3538, hlam]
                      · linarith only [h3236, h3538, hlam]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h2474, h3236, h3237, h3521, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h3236, hlam, p3524_0]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h3515, hlam, p3524_0]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h3517, hlam, p3524_0]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [hlam, p3524_0]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h3519, hlam, p3524_0]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h3236, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h3516, hlam, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h3518, hlam, p3524_0]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [h0, h3515, h3516, h3521, h3523, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3524_1]
                    · have p3524_0 := h3524c.1
                      have p3524_1 := h3524c.2.1
                      have p3524_2 := h3524c.2.2.1
                      have p3524_3 := h3524c.2.2.2
                      linarith only [hlam, p3524_0]
                  · linarith only [h0, h3236, h3521, h3523, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h3377, h3516, h3518, hlam]
          · linarith only [h0, h3236, h3377, h3517, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h3555 | h3555
          · rcases m.htr 0 3 5 (by decide) (by decide) with h3556 | h3556
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3557 | h3557
              · linarith only [h0, h3236, h3516, h3557, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3559 | h3559
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3560 | h3560
                  · rcases h0bigk with h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c | h3561c
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h0, hlam, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h2474, hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h0, h3377, h3559, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3237, hlam, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3377, h3559, hc01, hc12, hlam, hphi, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3377, hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3236, h3377, h3559, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3516, hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3236, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3377, h3559, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3377, h3515, h3559, h3560, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3377, h3515, h3516, h3559, h3560, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3236, hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3515, hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3555, hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3557, hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3236, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3515, h3516, h3560, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3556, hlam, p3561_0]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [h3377, h3515, h3556, h3559, h3560, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3561_1]
                    · have p3561_0 := h3561c.1
                      have p3561_1 := h3561c.2.1
                      have p3561_2 := h3561c.2.2.1
                      have p3561_3 := h3561c.2.2.2
                      linarith only [hlam, p3561_0]
                  · linarith only [h3377, h3555, h3560, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3588 | h3588
                  · rcases h0bigk with h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c | h3589c
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h0, hlam, p3589_1]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h2474, hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3589_1]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3237, hlam, p3589_1]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h0, h3559, hc01, hc23, hlam, hphi, ht12, p3589_1]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3377, hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h0, h3515, h3559, h3588, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3589_1]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3516, hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3236, h3377, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3589_1]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3377, hc02, hc23, hlam, hphi, p3589_1]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      rcases p3589_3 (m.d 0 1) (by simp) with h3603 | h3603
                      · linarith only [h2474, h3603, hlam]
                      · linarith only [h3236, h3603, hlam]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h2474, h3559, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3589_1, u5ehi0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3236, hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3515, hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3555, hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3557, hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3236, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p3589_1]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h0, h3236, h3516, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3589_1]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3556, hlam, p3589_0]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [h3515, h3557, h3588, hc34, hc45, hlam, hphi, p3589_1]
                    · have p3589_0 := h3589c.1
                      have p3589_1 := h3589c.2.1
                      have p3589_2 := h3589c.2.2.1
                      have p3589_3 := h3589c.2.2.2
                      linarith only [hlam, p3589_0]
                  · linarith only [h0, h3236, h3559, h3588, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h3618 | h3618
              · linarith only [h3236, h3237, h3618, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h3620 | h3620
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3621 | h3621
                  · rcases h0bigk with h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [hlam, p3622_0]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h0, hlam, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h2474, hlam, p3622_0]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h0, h3377, h3620, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3237, hlam, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3377, h3620, hc01, hc12, hlam, hphi, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [hlam, p3622_0]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3377, hlam, p3622_0]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3236, h3377, h3620, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3516, hlam, p3622_0]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3236, h3556, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3556, hc02, hc35, hlam, hphi, ht23, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [hlam, p3622_0]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3515, h3556, h3621, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3556, hlam, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3236, hlam, p3622_0]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3515, hlam, p3622_0]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3555, hlam, p3622_0]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [hlam, p3622_0]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3618, hlam, p3622_0]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3236, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3515, h3618, h3621, hc34, hc45, hlam, hphi, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3618, hc03, hc45, hlam, hphi, ht34, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [h3515, h3618, h3621, hc34, hc45, hlam, hphi, p3622_1]
                    · have p3622_0 := h3622c.1
                      have p3622_1 := h3622c.2.1
                      have p3622_2 := h3622c.2.2.1
                      have p3622_3 := h3622c.2.2.2
                      linarith only [hlam, p3622_0]
                  · linarith only [h0, h3236, h3377, h3555, h3621, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3649 | h3649
                  · rcases h0bigk with h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c | h3650c
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [hlam, p3650_0]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h0, hlam, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h2474, hlam, p3650_0]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h0, h3620, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3237, hlam, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h0, h3620, hc01, hc23, hlam, hphi, ht12, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [hlam, p3650_0]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3377, hlam, p3650_0]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3236, h3377, h3556, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3516, hlam, p3650_0]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3236, h3556, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3556, hc02, hc35, hlam, hphi, ht23, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [hlam, p3650_0]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3515, h3556, h3649, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3556, hlam, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3236, hlam, p3650_0]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3515, hlam, p3650_0]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3555, hlam, p3650_0]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [hlam, p3650_0]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3618, hlam, p3650_0]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3236, h3618, hc14, hc45, hlam, hphi, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3515, h3618, h3649, hc34, hc45, hlam, hphi, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3618, hc03, hc45, hlam, hphi, ht34, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [h3515, h3618, h3649, hc34, hc45, hlam, hphi, p3650_1]
                    · have p3650_0 := h3650c.1
                      have p3650_1 := h3650c.2.1
                      have p3650_2 := h3650c.2.2.1
                      have p3650_3 := h3650c.2.2.2
                      linarith only [hlam, p3650_0]
                  · linarith only [h0, h3236, h3620, h3649, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h0, h3236, h3377, h3555, hlam]
      · linarith only [h0, h3236, h3515, hlam]

set_option maxHeartbeats 9696000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_R_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2474 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3236 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3679 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h3680 | h3680
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3681 | h3681
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3682 | h3682
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3683 | h3683
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3684 | h3684
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3685 | h3685
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3686 | h3686
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3687 | h3687
                · rcases h0bigk with h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c | h3688c
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [hlam, p3688_0]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h0, hlam, p3688_1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h2474, hlam, p3688_0]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h3236, hlam, p3688_1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [hc01, hlam, hphi, ht0b, ht5b, p3688_1, u5ehi0]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p3688_1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [hlam, p3688_0]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h0, h3684, hc12, hlam, hphi, ht01, ht0b, ht5b, p3688_1, u5ehi3]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h0, h3236, h3679, hc12, hlam, hphi, ht01, ht0b, ht5b, p3688_1, u5ehi1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h0, h3679, hc12, hlam, hphi, ht01, ht0b, ht5b, p3688_1, u5ehi1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h3679, hc03, hlam, hphi, ht0b, ht5b, p3688_1, u5ehi1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h3680, hlam, p3688_1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [hlam, p3688_0]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h2474, h3236, h3679, h3686, hc12, hlam, hphi, ht01, ht0b, ht5b, p3688_1, u5ehi1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h2474, h3679, h3686, hc12, hlam, hphi, ht01, ht0b, ht5b, p3688_1, u5ehi1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h3679, hc04, hlam, hphi, ht0b, ht5b, p3688_1, u5ehi1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h3681, hlam, p3688_0]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h3683, hlam, p3688_0]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [hlam, p3688_0]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h2474, h3679, h3683, h3686, hc12, hlam, hphi, ht01, ht0b, ht5b, p3688_1, u5ehi1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h3679, hlam, p3688_0]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h3682, hlam, p3688_1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h3684, hlam, p3688_0]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [h3685, hlam, p3688_1]
                  · have p3688_0 := h3688c.1
                    have p3688_1 := h3688c.2.1
                    have p3688_2 := h3688c.2.2.1
                    have p3688_3 := h3688c.2.2.2
                    linarith only [hlam, p3688_0]
                · rcases h0bigk with h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c | h3714c
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [hlam, p3714_0]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h0, hlam, p3714_1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h2474, hlam, p3714_0]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h3236, hlam, p3714_1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h3679, hc01, hlam, hphi, ht0b, ht5b, p3714_1, u5ehi1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p3714_1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [hlam, p3714_0]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h0, h3683, h3687, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3714_1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h0, h3236, h3679, hc12, hlam, hphi, ht01, ht0b, ht5b, p3714_1, u5ehi1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h0, h3679, hc12, hlam, hphi, ht01, ht0b, ht5b, p3714_1, u5ehi1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h3679, hc03, hlam, hphi, ht0b, ht5b, p3714_1, u5ehi1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h3680, hlam, p3714_1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [hlam, p3714_0]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h2474, h3236, h3679, h3686, hc12, hlam, hphi, ht01, ht0b, ht5b, p3714_1, u5ehi1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h2474, h3679, h3686, hc12, hlam, hphi, ht01, ht0b, ht5b, p3714_1, u5ehi1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h3679, hc04, hlam, hphi, ht0b, ht5b, p3714_1, u5ehi1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h3681, hlam, p3714_0]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h3683, hlam, p3714_0]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [hlam, p3714_0]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h2474, h3679, h3683, h3686, hc12, hlam, hphi, ht01, ht0b, ht5b, p3714_1, u5ehi1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h3679, hlam, p3714_0]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h3682, hlam, p3714_1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h3684, hlam, p3714_0]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [h3685, hlam, p3714_1]
                  · have p3714_0 := h3714c.1
                    have p3714_1 := h3714c.2.1
                    have p3714_2 := h3714c.2.2.1
                    have p3714_3 := h3714c.2.2.2
                    linarith only [hlam, p3714_0]
              · linarith only [h0, h3679, h3686, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h3236, h3679, h3685, hlam]
          · linarith only [h2474, h3679, h3684, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3743 | h3743
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3744 | h3744
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3745 | h3745
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3746 | h3746
                · linarith only [h2474, h3679, h3680, h3683, h3746, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                · rcases h0bigk with h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c | h3748c
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [hlam, p3748_0]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h0, hlam, p3748_1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h2474, hlam, p3748_0]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3236, hlam, p3748_1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [hc01, hlam, hphi, ht0b, ht5b, p3748_1, u5ehi0]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p3748_1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [hlam, p3748_0]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h0, h3743, hc12, hlam, hphi, ht01, ht0b, ht5b, p3748_1, u5ehi3]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h0, h3744, hc12, hlam, hphi, ht01, ht0b, ht5b, p3748_1, u5ehi4]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h0, h3679, hc12, hlam, hphi, ht01, ht0b, ht5b, p3748_1, u5ehi1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3679, hc03, hlam, hphi, ht0b, ht5b, p3748_1, u5ehi1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3680, hlam, p3748_1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [hlam, p3748_0]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3683, hlam, p3748_1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3679, h3683, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3748_1, u5ehi1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3679, hc04, hlam, hphi, ht0b, ht5b, p3748_1, u5ehi1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3681, hlam, p3748_0]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3683, hc03, hc34, hlam, hphi, p3748_1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [hlam, p3748_0]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3679, h3683, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3748_1, u5ehi1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3679, hlam, p3748_0]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3682, hlam, p3748_1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3743, hlam, p3748_0]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [h3744, hlam, p3748_1]
                  · have p3748_0 := h3748c.1
                    have p3748_1 := h3748c.2.1
                    have p3748_2 := h3748c.2.2.1
                    have p3748_3 := h3748c.2.2.2
                    linarith only [hlam, p3748_0]
              · linarith only [h0, h3679, h3745, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h3236, h3679, h3744, hlam]
          · linarith only [h2474, h3679, h3743, hlam]
      · linarith only [h0, h3679, h3682, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3778 | h3778
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3779 | h3779
        · linarith only [h3680, h3681, h3779, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3781 | h3781
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3782 | h3782
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3783 | h3783
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3784 | h3784
                · linarith only [h2474, h3679, h3680, h3779, h3784, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                · rcases h0bigk with h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c | h3786c
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [hlam, p3786_0]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h0, hlam, p3786_1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h2474, hlam, p3786_0]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3236, hlam, p3786_1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [hc01, hlam, hphi, ht0b, ht5b, p3786_1, u5ehi0]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3681, h3784, hc01, hc34, hlam, hphi, ht12, ht23, p3786_1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [hlam, p3786_0]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3681, h3784, hc03, hc34, hlam, hphi, p3786_1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3681, hlam, p3786_1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3681, h3782, h3784, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3786_1, u5ehi4]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3679, hc03, hlam, hphi, ht0b, ht5b, p3786_1, u5ehi1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3680, hlam, p3786_1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [hlam, p3786_0]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3779, hlam, p3786_1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3680, h3681, h3782, h3784, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3786_1, u5ehi4]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3679, h3681, h3784, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3786_1, u5ehi1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3681, h3784, hc02, hc34, hlam, hphi, ht23, p3786_1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h2474, h3679, h3681, h3784, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3786_1, u5ehi1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [hlam, p3786_0]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3681, h3782, h3784, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3786_1, u5ehi4]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3679, hlam, p3786_0]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3778, hlam, p3786_1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3781, hlam, p3786_0]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [h3782, hlam, p3786_1]
                  · have p3786_0 := h3786c.1
                    have p3786_1 := h3786c.2.1
                    have p3786_2 := h3786c.2.2.1
                    have p3786_3 := h3786c.2.2.2
                    linarith only [hlam, p3786_0]
              · linarith only [h0, h3679, h3783, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h3236, h3679, h3782, hlam]
          · linarith only [h2474, h3679, h3781, hlam]
      · linarith only [h2474, h3679, h3680, h3778, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3816 | h3816
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3817 | h3817
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3818 | h3818
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3819 | h3819
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3820 | h3820
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3821 | h3821
              · linarith only [h3680, h3817, h3821, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h3679, h3821, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h3236, h3679, h3820, hlam]
          · linarith only [h3236, h3679, h3680, h3816, h3819, hlam]
        · linarith only [h3680, h3816, h3818, hlam]
      · linarith only [h3236, h3679, h3816, h3817, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3828 | h3828
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3829 | h3829
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3830 | h3830
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3831 | h3831
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3832 | h3832
              · linarith only [h3680, h3828, h3832, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h3679, h3832, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h3236, h3679, h3831, hlam]
          · linarith only [h2474, h3679, h3830, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3837 | h3837
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3838 | h3838
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3839 | h3839
              · linarith only [h0, h3679, h3680, h3839, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
              · linarith only [h0, h3679, h3839, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h3679, h3680, h3829, h3838, hlam]
          · linarith only [h0, h3679, h3680, h3837, hlam]
      · linarith only [h0, h3679, h3828, hlam]

end R2N4
