import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 2) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 2) ∧ (m.d 1 5) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 5) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  rcases p9633_3 (m.d 0 1) (by simp) with h9992 | h9992
  · rcases p9633_3 (m.d 1 2) (by simp) with h9993 | h9993
    · rcases p9633_3 (m.d 1 3) (by simp) with h9994 | h9994
      · linarith only [h9268, h9994, hlam]
      · rcases p9633_3 (m.d 1 4) (by simp) with h9996 | h9996
        · linarith only [h9269, h9996, hlam]
        · rcases p9633_3 (m.d 1 5) (by simp) with h9998 | h9998
          · linarith only [h9270, h9998, hlam]
          · rcases h1emax with h10000 | h10000 | h10000 | h10000 | h10000
            · linarith only [h0, h10000, h9271, h9623, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9633_1]
            · linarith only [h10000, h9268, h9271, h9623, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9633_1]
            · rcases h2bigk with h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c | h10003c
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h9268, h9271, h9623, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10003_1, p9633_1]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                rcases p10003_3 (m.d 0 2) (by simp) with h10006 | h10006
                · rcases p10003_3 (m.d 1 2) (by simp) with h10007 | h10007
                  · linarith only [h0, h10007, hlam]
                  · linarith only [h10007, h9268, hlam]
                · linarith only [h10006, hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                rcases p10003_3 (m.d 0 2) (by simp) with h10011 | h10011
                · rcases p10003_3 (m.d 1 2) (by simp) with h10012 | h10012
                  · linarith only [h0, h10012, hlam]
                  · linarith only [h10012, h9269, hlam]
                · linarith only [h10011, hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                rcases p10003_3 (m.d 0 2) (by simp) with h10016 | h10016
                · rcases p10003_3 (m.d 1 2) (by simp) with h10017 | h10017
                  · linarith only [h0, h10017, hlam]
                  · linarith only [h10017, h9270, hlam]
                · linarith only [h10016, hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h0, hlam, p10003_1]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                rcases p10003_3 (m.d 0 2) (by simp) with h10023 | h10023
                · rcases p10003_3 (m.d 1 2) (by simp) with h10024 | h10024
                  · rcases p10003_3 (m.d 2 3) (by simp) with h10025 | h10025
                    · linarith only [h10025, hlam, p10003_0]
                    · rcases p10003_3 (m.d 2 4) (by simp) with h10027 | h10027
                      · linarith only [h10027, h9269, hlam]
                      · linarith only [h10027, h9625, hlam]
                  · linarith only [h10024, hlam, p10003_0]
                · linarith only [h10023, h4, hlam]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                rcases p10003_3 (m.d 0 2) (by simp) with h10032 | h10032
                · rcases p10003_3 (m.d 1 2) (by simp) with h10033 | h10033
                  · rcases p10003_3 (m.d 2 3) (by simp) with h10034 | h10034
                    · linarith only [h10034, h9268, hlam]
                    · rcases p10003_3 (m.d 2 4) (by simp) with h10036 | h10036
                      · linarith only [h10036, hlam, p10003_0]
                      · rcases p10003_3 (m.d 2 5) (by simp) with h10038 | h10038
                        · linarith only [h10038, h9270, hlam]
                        · linarith only [h10038, h9629, hlam]
                  · linarith only [h10033, hlam, p10003_0]
                · linarith only [h10032, h5, hlam]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                rcases p10003_3 (m.d 0 2) (by simp) with h10043 | h10043
                · rcases p10003_3 (m.d 1 2) (by simp) with h10044 | h10044
                  · rcases p10003_3 (m.d 2 3) (by simp) with h10045 | h10045
                    · linarith only [h10045, h9268, hlam]
                    · rcases p10003_3 (m.d 2 4) (by simp) with h10047 | h10047
                      · linarith only [h10047, h9269, hlam]
                      · rcases p10003_3 (m.d 2 5) (by simp) with h10049 | h10049
                        · linarith only [h10049, hlam, p10003_0]
                        · rcases h4bigk with h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c | h10051c
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10051_1]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9, h9625, hc23, hc45, hlam, hphi, ht34, p10051_1]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10051_1]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9, hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h2, hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9623, h9625, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10051_1, p9633_1]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9271, hlam, p10051_1]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9623, hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h5, hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9269, hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9625, hlam, p10051_1]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9629, hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h7, hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h7, h9, hc14, hc45, hlam, hphi, p10051_1]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h7, h9, h9625, hc23, hc45, hlam, hphi, ht34, p10051_1]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9631, hlam, p10051_0]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h7, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10051_1]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            rcases p10051_3 (m.d 0 4) (by simp) with h10073 | h10073
                            · linarith only [h10073, h9, hlam]
                            · linarith only [h10073, h2, hlam]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            rcases p10051_3 (m.d 0 4) (by simp) with h10076 | h10076
                            · linarith only [h10076, h9, hlam]
                            · linarith only [h10076, h5, hlam]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10051_1]
                          · have p10051_0 := h10051c.1
                            have p10051_1 := h10051c.2.1
                            have p10051_2 := h10051c.2.2.1
                            have p10051_3 := h10051c.2.2.2
                            linarith only [hlam, p10051_0]
                  · linarith only [h10044, hlam, p10003_0]
                · linarith only [h10043, h6, hlam]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h4, hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h9268, hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h9625, hlam, p10003_1]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h9627, hlam, p10003_1]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h5, hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h9269, hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h2, h9, h9269, hc23, hc45, hlam, hphi, ht34, p10003_1]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h9629, hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h6, hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h9270, hlam, p10003_0]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h0, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10003_1, p9633_1]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [h0, h9270, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p10003_1, p9633_1]
              · have p10003_0 := h10003c.1
                have p10003_1 := h10003c.2.1
                have p10003_2 := h10003c.2.2.1
                have p10003_3 := h10003c.2.2.2
                linarith only [hlam, p10003_0]
            · rcases h2bigk with h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c | h10098c
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h9623, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p10098_1, p9633_1]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                rcases p10098_3 (m.d 0 2) (by simp) with h10101 | h10101
                · rcases p10098_3 (m.d 1 2) (by simp) with h10102 | h10102
                  · linarith only [h0, h10102, hlam]
                  · linarith only [h10102, h9268, hlam]
                · linarith only [h10101, hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                rcases p10098_3 (m.d 0 2) (by simp) with h10106 | h10106
                · rcases p10098_3 (m.d 1 2) (by simp) with h10107 | h10107
                  · linarith only [h0, h10107, hlam]
                  · linarith only [h10107, h9269, hlam]
                · linarith only [h10106, hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                rcases p10098_3 (m.d 0 2) (by simp) with h10111 | h10111
                · rcases p10098_3 (m.d 1 2) (by simp) with h10112 | h10112
                  · linarith only [h0, h10112, hlam]
                  · linarith only [h10112, h9270, hlam]
                · linarith only [h10111, hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h0, hlam, p10098_1]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                rcases p10098_3 (m.d 0 2) (by simp) with h10118 | h10118
                · rcases p10098_3 (m.d 1 2) (by simp) with h10119 | h10119
                  · rcases p10098_3 (m.d 2 3) (by simp) with h10120 | h10120
                    · linarith only [h10120, hlam, p10098_0]
                    · rcases p10098_3 (m.d 2 4) (by simp) with h10122 | h10122
                      · linarith only [h10122, h9269, hlam]
                      · linarith only [h10122, h9625, hlam]
                  · linarith only [h10119, hlam, p10098_0]
                · linarith only [h10118, h4, hlam]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                rcases p10098_3 (m.d 0 2) (by simp) with h10127 | h10127
                · rcases p10098_3 (m.d 1 2) (by simp) with h10128 | h10128
                  · rcases p10098_3 (m.d 2 3) (by simp) with h10129 | h10129
                    · linarith only [h10129, h9268, hlam]
                    · rcases p10098_3 (m.d 2 4) (by simp) with h10131 | h10131
                      · linarith only [h10131, hlam, p10098_0]
                      · rcases p10098_3 (m.d 2 5) (by simp) with h10133 | h10133
                        · linarith only [h10133, h9270, hlam]
                        · linarith only [h10133, h9629, hlam]
                  · linarith only [h10128, hlam, p10098_0]
                · linarith only [h10127, h5, hlam]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                rcases p10098_3 (m.d 0 2) (by simp) with h10138 | h10138
                · rcases p10098_3 (m.d 1 2) (by simp) with h10139 | h10139
                  · rcases p10098_3 (m.d 2 3) (by simp) with h10140 | h10140
                    · linarith only [h10140, h9268, hlam]
                    · rcases p10098_3 (m.d 2 4) (by simp) with h10142 | h10142
                      · linarith only [h10142, h9269, hlam]
                      · rcases p10098_3 (m.d 2 5) (by simp) with h10144 | h10144
                        · linarith only [h10144, hlam, p10098_0]
                        · rcases h4bigk with h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c | h10146c
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9, h9269, h9625, hc23, hc45, hlam, hphi, ht34, p10146_1]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9, h9625, hc23, hc45, hlam, hphi, ht34, p10146_1]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10146_1]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9, hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h2, hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9623, h9625, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10146_1, p9633_1]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9271, hlam, p10146_1]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9623, hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h5, hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9269, hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9625, hlam, p10146_1]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9629, hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h7, hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h7, h9, hc14, hc45, hlam, hphi, p10146_1]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h7, h9, h9625, hc23, hc45, hlam, hphi, ht34, p10146_1]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9631, hlam, p10146_0]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h7, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10146_1]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            rcases p10146_3 (m.d 0 4) (by simp) with h10168 | h10168
                            · linarith only [h10168, h9, hlam]
                            · linarith only [h10168, h2, hlam]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            rcases p10146_3 (m.d 0 4) (by simp) with h10171 | h10171
                            · linarith only [h10171, h9, hlam]
                            · linarith only [h10171, h5, hlam]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10146_1]
                          · have p10146_0 := h10146c.1
                            have p10146_1 := h10146c.2.1
                            have p10146_2 := h10146c.2.2.1
                            have p10146_3 := h10146c.2.2.2
                            linarith only [hlam, p10146_0]
                  · linarith only [h10139, hlam, p10098_0]
                · linarith only [h10138, h6, hlam]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h4, hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h9268, hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h9625, hlam, p10098_1]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h9627, hlam, p10098_1]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h5, hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h9269, hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h2, h9, h9269, hc23, hc45, hlam, hphi, ht34, p10098_1]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h9629, hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h6, hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h9270, hlam, p10098_0]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h0, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10098_1, p9633_1]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [h0, h9270, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p10098_1, p9633_1]
              · have p10098_0 := h10098c.1
                have p10098_1 := h10098c.2.1
                have p10098_2 := h10098c.2.2.1
                have p10098_3 := h10098c.2.2.2
                linarith only [hlam, p10098_0]
            · rcases h2bigk with h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c | h10193c
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h9623, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p10193_1, p9633_1]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                rcases p10193_3 (m.d 0 2) (by simp) with h10196 | h10196
                · rcases p10193_3 (m.d 1 2) (by simp) with h10197 | h10197
                  · linarith only [h0, h10197, hlam]
                  · linarith only [h10197, h9268, hlam]
                · linarith only [h10196, hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                rcases p10193_3 (m.d 0 2) (by simp) with h10201 | h10201
                · rcases p10193_3 (m.d 1 2) (by simp) with h10202 | h10202
                  · linarith only [h0, h10202, hlam]
                  · linarith only [h10202, h9269, hlam]
                · linarith only [h10201, hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                rcases p10193_3 (m.d 0 2) (by simp) with h10206 | h10206
                · rcases p10193_3 (m.d 1 2) (by simp) with h10207 | h10207
                  · linarith only [h0, h10207, hlam]
                  · linarith only [h10207, h9270, hlam]
                · linarith only [h10206, hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h0, hlam, p10193_1]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                rcases p10193_3 (m.d 0 2) (by simp) with h10213 | h10213
                · rcases p10193_3 (m.d 1 2) (by simp) with h10214 | h10214
                  · rcases p10193_3 (m.d 2 3) (by simp) with h10215 | h10215
                    · linarith only [h10215, hlam, p10193_0]
                    · rcases p10193_3 (m.d 2 4) (by simp) with h10217 | h10217
                      · linarith only [h10217, h9269, hlam]
                      · linarith only [h10217, h9625, hlam]
                  · linarith only [h10214, hlam, p10193_0]
                · linarith only [h10213, h4, hlam]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                rcases p10193_3 (m.d 0 2) (by simp) with h10222 | h10222
                · rcases p10193_3 (m.d 1 2) (by simp) with h10223 | h10223
                  · rcases p10193_3 (m.d 2 3) (by simp) with h10224 | h10224
                    · linarith only [h10224, h9268, hlam]
                    · rcases p10193_3 (m.d 2 4) (by simp) with h10226 | h10226
                      · linarith only [h10226, hlam, p10193_0]
                      · rcases p10193_3 (m.d 2 5) (by simp) with h10228 | h10228
                        · linarith only [h10228, h9270, hlam]
                        · linarith only [h10228, h9629, hlam]
                  · linarith only [h10223, hlam, p10193_0]
                · linarith only [h10222, h5, hlam]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                rcases p10193_3 (m.d 0 2) (by simp) with h10233 | h10233
                · rcases p10193_3 (m.d 1 2) (by simp) with h10234 | h10234
                  · rcases p10193_3 (m.d 2 3) (by simp) with h10235 | h10235
                    · linarith only [h10235, h9268, hlam]
                    · rcases p10193_3 (m.d 2 4) (by simp) with h10237 | h10237
                      · linarith only [h10237, h9269, hlam]
                      · rcases p10193_3 (m.d 2 5) (by simp) with h10239 | h10239
                        · linarith only [h10239, hlam, p10193_0]
                        · rcases h4bigk with h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c | h10241c
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9, h9269, h9625, hc23, hc45, hlam, hphi, ht34, p10241_1]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9, h9625, hc23, hc45, hlam, hphi, ht34, p10241_1]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10241_1]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9, hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h2, hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9623, h9625, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10241_1, p9633_1]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9271, hlam, p10241_1]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9623, hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h5, hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9269, hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9625, hlam, p10241_1]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9629, hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h7, hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h7, h9, hc14, hc45, hlam, hphi, p10241_1]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h7, h9, h9625, hc23, hc45, hlam, hphi, ht34, p10241_1]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9631, hlam, p10241_0]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h7, h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10241_1]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            rcases p10241_3 (m.d 0 4) (by simp) with h10263 | h10263
                            · linarith only [h10263, h9, hlam]
                            · linarith only [h10263, h2, hlam]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            rcases p10241_3 (m.d 0 4) (by simp) with h10266 | h10266
                            · linarith only [h10266, h9, hlam]
                            · linarith only [h10266, h5, hlam]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [h9268, h9271, hc23, hc45, hlam, hphi, ht34, p10241_1]
                          · have p10241_0 := h10241c.1
                            have p10241_1 := h10241c.2.1
                            have p10241_2 := h10241c.2.2.1
                            have p10241_3 := h10241c.2.2.2
                            linarith only [hlam, p10241_0]
                  · linarith only [h10234, hlam, p10193_0]
                · linarith only [h10233, h6, hlam]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h4, hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h9268, hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h9625, hlam, p10193_1]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h9627, hlam, p10193_1]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h5, hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h9269, hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h2, h9, h9269, hc23, hc45, hlam, hphi, ht34, p10193_1]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h9629, hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h6, hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h9270, hlam, p10193_0]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h0, h9270, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10193_1, p9633_1]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [h0, h9270, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p10193_1, p9633_1]
              · have p10193_0 := h10193c.1
                have p10193_1 := h10193c.2.1
                have p10193_2 := h10193c.2.2.1
                have p10193_3 := h10193c.2.2.2
                linarith only [hlam, p10193_0]
    · linarith only [h9270, h9993, hlam]
  · linarith only [h3, h9992, hlam]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 3) ∧ (m.d 0 1) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 0 1) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [h1, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 3) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 3) ∧ (m.d 1 2) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 2) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [h9268, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 3) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 3) ∧ (m.d 1 3) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 3) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x13 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 3) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 3) ∧ (m.d 1 4) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 4) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [h9271, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x14 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 3) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 3) ∧ (m.d 1 5) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 5) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [h9619, hlam, p9633_1]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x15 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 4) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 4) ∧ (m.d 0 1) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 0 1) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [h2, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x16 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 4) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 4) ∧ (m.d 1 2) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 2) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [h9269, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x17 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 4) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 4) ∧ (m.d 1 3) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 3) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [h2, h9, h9268, hc23, hc45, hlam, hphi, ht34, p9633_1]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x18 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 4) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 4) ∧ (m.d 1 4) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 4) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x19 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 4) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 4) ∧ (m.d 1 5) - (m.d 1 4) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 4) ∨ (m.d 1 5) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [h9623, hlam, p9633_1]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x20 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 5) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 5) ∧ (m.d 0 1) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 0 1) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [h3, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x21 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 5) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 5) ∧ (m.d 1 2) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 2) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [h9270, hlam, p9633_0]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x22 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 1 5) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 5) ∧ (m.d 1 3) - (m.d 1 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 5) ∨ (m.d 1 3) ≤ z)))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  rcases p9633_3 (m.d 0 1) (by simp) with h10302 | h10302
  · rcases p9633_3 (m.d 1 2) (by simp) with h10303 | h10303
    · rcases p9633_3 (m.d 1 3) (by simp) with h10304 | h10304
      · linarith only [h10304, h9619, hlam]
      · rcases p9633_3 (m.d 1 4) (by simp) with h10306 | h10306
        · linarith only [h10306, h9623, hlam]
        · linarith only [h10306, h9271, hlam]
    · linarith only [h10303, h9268, hlam]
  · linarith only [h1, h10302, hlam]

end R2N4
