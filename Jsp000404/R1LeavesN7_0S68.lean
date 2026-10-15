import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 1 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 2) ∧ (m.d 0 1) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 0 1) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  rcases p35197_3 (m.d 0 1) (by simp) with h35506 | h35506
  · linarith only [h35506, hlam, p35197_0]
  · rcases p35197_3 (m.d 1 2) (by simp) with h35508 | h35508
    · rcases p35197_3 (m.d 1 3) (by simp) with h35509 | h35509
      · linarith only [h34261, h35509, hlam]
      · rcases p35197_3 (m.d 1 4) (by simp) with h35511 | h35511
        · linarith only [h34262, h35511, hlam]
        · rcases p35197_3 (m.d 1 5) (by simp) with h35513 | h35513
          · linarith only [h34263, h35513, hlam]
          · rcases h1emax with h35515 | h35515 | h35515 | h35515 | h35515
            · rcases h2bigk with h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c | h35516c
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h0, hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                rcases p35516_3 (m.d 0 2) (by simp) with h35519 | h35519
                · rcases p35516_3 (m.d 1 2) (by simp) with h35520 | h35520
                  · rcases p35516_3 (m.d 2 3) (by simp) with h35521 | h35521
                    · linarith only [h35521, hlam, p35516_0]
                    · rcases p35516_3 (m.d 2 4) (by simp) with h35523 | h35523
                      · linarith only [h33191, h35523, hlam]
                      · linarith only [h34270, h35523, hlam]
                  · linarith only [h34261, h35520, hlam]
                · linarith only [h35519, hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                rcases p35516_3 (m.d 0 2) (by simp) with h35528 | h35528
                · rcases p35516_3 (m.d 1 2) (by simp) with h35529 | h35529
                  · rcases p35516_3 (m.d 2 3) (by simp) with h35530 | h35530
                    · linarith only [h33190, h35530, hlam]
                    · rcases p35516_3 (m.d 2 4) (by simp) with h35532 | h35532
                      · linarith only [h35532, hlam, p35516_0]
                      · rcases p35516_3 (m.d 2 5) (by simp) with h35534 | h35534
                        · linarith only [h33192, h35534, hlam]
                        · linarith only [h34274, h35534, hlam]
                  · linarith only [h34262, h35529, hlam]
                · linarith only [h35528, hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                rcases p35516_3 (m.d 0 2) (by simp) with h35539 | h35539
                · rcases p35516_3 (m.d 1 2) (by simp) with h35540 | h35540
                  · rcases p35516_3 (m.d 2 3) (by simp) with h35541 | h35541
                    · linarith only [h33190, h35541, hlam]
                    · rcases p35516_3 (m.d 2 4) (by simp) with h35543 | h35543
                      · linarith only [h33191, h35543, hlam]
                      · rcases p35516_3 (m.d 2 5) (by simp) with h35545 | h35545
                        · linarith only [h35545, hlam, p35516_0]
                        · rcases h4bigk with h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c | h35547c
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [hlam, p35547_0]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h33188, h34261, h34264, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35547_1]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35547_1]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h33193, hlam, p35547_1]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h33836, hlam, p35547_0]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h33188, hlam, p35547_0]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [hlam, p35547_0]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35547_1]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h34264, hlam, p35547_1]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h34268, hlam, p35547_0]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h33191, hlam, p35547_0]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h34262, hlam, p35547_0]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [hlam, p35547_0]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h34270, hlam, p35547_1]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h34274, hlam, p35547_0]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h34276, hc04, hc45, hlam, hphi, p35547_1]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35547_1]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35547_1]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [hlam, p35547_0]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h34276, hlam, p35547_0]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            rcases p35547_3 (m.d 0 4) (by simp) with h35568 | h35568
                            · linarith only [h35568, hlam, p35547_0]
                            · rcases p35547_3 (m.d 1 4) (by simp) with h35570 | h35570
                              · linarith only [h34268, h35570, hlam]
                              · rcases p35547_3 (m.d 2 4) (by simp) with h35572 | h35572
                                · linarith only [h34274, h35572, hlam]
                                · rcases p35547_3 (m.d 3 4) (by simp) with h35574 | h35574
                                  · linarith only [h34276, h35574, hlam]
                                  · linarith only [h33193, h35574, hlam]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            rcases p35547_3 (m.d 0 4) (by simp) with h35577 | h35577
                            · linarith only [h33836, h35577, hlam]
                            · linarith only [h33188, h35577, hlam]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            rcases p35547_3 (m.d 0 4) (by simp) with h35580 | h35580
                            · linarith only [h33836, h35580, hlam]
                            · linarith only [h33191, h35580, hlam]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [h33187, h33193, h34261, hc23, hc45, hlam, hphi, ht34, p35547_1]
                          · have p35547_0 := h35547c.1
                            have p35547_1 := h35547c.2.1
                            have p35547_2 := h35547c.2.2.1
                            have p35547_3 := h35547c.2.2.2
                            linarith only [hlam, p35547_0]
                  · linarith only [h34263, h35540, hlam]
                · linarith only [h35539, hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                rcases p35516_3 (m.d 0 2) (by simp) with h35587 | h35587
                · linarith only [h0, h35587, hlam]
                · rcases p35516_3 (m.d 1 2) (by simp) with h35589 | h35589
                  · rcases p35516_3 (m.d 2 3) (by simp) with h35590 | h35590
                    · linarith only [h34261, h35590, hlam]
                    · rcases p35516_3 (m.d 2 4) (by simp) with h35592 | h35592
                      · linarith only [h34262, h35592, hlam]
                      · rcases p35516_3 (m.d 2 5) (by simp) with h35594 | h35594
                        · linarith only [h34263, h35594, hlam]
                        · rcases h4bigk with h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c | h35596c
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [hlam, p35596_0]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h0, h33188, h34262, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35516_1, p35596_1]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35516_1, p35596_1]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h33193, hlam, p35596_1]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h33836, hlam, p35596_0]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h33188, hlam, p35596_0]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [hlam, p35596_0]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35516_1, p35596_1]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h34264, hlam, p35596_1]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h34268, hlam, p35596_0]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h33191, hlam, p35596_0]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h34262, hlam, p35596_0]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [hlam, p35596_0]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h34270, hlam, p35596_1]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h34274, hlam, p35596_0]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h33187, h33193, h34261, h34276, hc23, hc45, hlam, hphi, ht34, p35596_1]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35596_1]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35596_1]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [hlam, p35596_0]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h34276, hlam, p35596_0]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            rcases p35596_3 (m.d 0 4) (by simp) with h35617 | h35617
                            · linarith only [h35617, hlam, p35596_0]
                            · rcases p35596_3 (m.d 1 4) (by simp) with h35619 | h35619
                              · linarith only [h34268, h35619, hlam]
                              · rcases p35596_3 (m.d 2 4) (by simp) with h35621 | h35621
                                · linarith only [h34274, h35621, hlam]
                                · rcases p35596_3 (m.d 3 4) (by simp) with h35623 | h35623
                                  · linarith only [h34276, h35623, hlam]
                                  · linarith only [h33193, h35623, hlam]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            rcases p35596_3 (m.d 0 4) (by simp) with h35626 | h35626
                            · linarith only [h33836, h35626, hlam]
                            · linarith only [h33188, h35626, hlam]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            rcases p35596_3 (m.d 0 4) (by simp) with h35629 | h35629
                            · linarith only [h33836, h35629, hlam]
                            · linarith only [h33191, h35629, hlam]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [h33187, h33193, h34261, hc23, hc45, hlam, hphi, ht34, p35596_1]
                          · have p35596_0 := h35596c.1
                            have p35596_1 := h35596c.2.1
                            have p35596_2 := h35596c.2.2.1
                            have p35596_3 := h35596c.2.2.2
                            linarith only [hlam, p35596_0]
                  · linarith only [h0, h35589, hlam]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h33187, h34261, hlam, p35197_1, p35516_2]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h33188, h34262, hlam, p35197_1, p35516_2]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h33189, h34263, hlam, p35197_1, p35516_2]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h33190, hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h34261, hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h34270, hlam, p35516_1]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h34272, hlam, p35516_1]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h33191, hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h34262, hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h33188, h34262, h35515, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35516_1]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h34274, hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h33192, hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h34263, hlam, p35516_0]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h33189, h34263, h35515, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35516_1]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [h33189, h34263, h35515, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p35516_1]
              · have p35516_0 := h35516c.1
                have p35516_1 := h35516c.2.1
                have p35516_2 := h35516c.2.2.1
                have p35516_3 := h35516c.2.2.2
                linarith only [hlam, p35516_0]
            · linarith only [h35515, hc01, hlam, p35197_1]
            · rcases h2bigk with h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c | h35655c
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h0, hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                rcases p35655_3 (m.d 0 2) (by simp) with h35658 | h35658
                · rcases p35655_3 (m.d 1 2) (by simp) with h35659 | h35659
                  · rcases p35655_3 (m.d 2 3) (by simp) with h35660 | h35660
                    · linarith only [h35660, hlam, p35655_0]
                    · rcases p35655_3 (m.d 2 4) (by simp) with h35662 | h35662
                      · linarith only [h33191, h35662, hlam]
                      · linarith only [h34270, h35662, hlam]
                  · linarith only [h34261, h35659, hlam]
                · linarith only [h35658, hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                rcases p35655_3 (m.d 0 2) (by simp) with h35667 | h35667
                · rcases p35655_3 (m.d 1 2) (by simp) with h35668 | h35668
                  · rcases p35655_3 (m.d 2 3) (by simp) with h35669 | h35669
                    · linarith only [h33190, h35669, hlam]
                    · rcases p35655_3 (m.d 2 4) (by simp) with h35671 | h35671
                      · linarith only [h35671, hlam, p35655_0]
                      · rcases p35655_3 (m.d 2 5) (by simp) with h35673 | h35673
                        · linarith only [h33192, h35673, hlam]
                        · linarith only [h34274, h35673, hlam]
                  · linarith only [h34262, h35668, hlam]
                · linarith only [h35667, hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                rcases p35655_3 (m.d 0 2) (by simp) with h35678 | h35678
                · rcases p35655_3 (m.d 1 2) (by simp) with h35679 | h35679
                  · rcases p35655_3 (m.d 2 3) (by simp) with h35680 | h35680
                    · linarith only [h33190, h35680, hlam]
                    · rcases p35655_3 (m.d 2 4) (by simp) with h35682 | h35682
                      · linarith only [h33191, h35682, hlam]
                      · rcases p35655_3 (m.d 2 5) (by simp) with h35684 | h35684
                        · linarith only [h35684, hlam, p35655_0]
                        · rcases h4bigk with h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c | h35686c
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [hlam, p35686_0]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h33188, h34262, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35686_1]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35686_1]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h33193, hlam, p35686_1]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h33836, hlam, p35686_0]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h33188, hlam, p35686_0]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [hlam, p35686_0]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35686_1]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h34264, hlam, p35686_1]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h34268, hlam, p35686_0]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h33191, hlam, p35686_0]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h34262, hlam, p35686_0]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [hlam, p35686_0]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h34270, hlam, p35686_1]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h34274, hlam, p35686_0]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h34276, hc04, hc45, hlam, hphi, p35686_1]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h34276, hc14, hc45, hlam, hphi, p35686_1]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35686_1]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [hlam, p35686_0]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h34276, hlam, p35686_0]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            rcases p35686_3 (m.d 0 4) (by simp) with h35707 | h35707
                            · linarith only [h35707, hlam, p35686_0]
                            · rcases p35686_3 (m.d 1 4) (by simp) with h35709 | h35709
                              · linarith only [h34268, h35709, hlam]
                              · rcases p35686_3 (m.d 2 4) (by simp) with h35711 | h35711
                                · linarith only [h34274, h35711, hlam]
                                · rcases p35686_3 (m.d 3 4) (by simp) with h35713 | h35713
                                  · linarith only [h34276, h35713, hlam]
                                  · linarith only [h33193, h35713, hlam]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            rcases p35686_3 (m.d 0 4) (by simp) with h35716 | h35716
                            · linarith only [h33836, h35716, hlam]
                            · linarith only [h33188, h35716, hlam]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            rcases p35686_3 (m.d 0 4) (by simp) with h35719 | h35719
                            · linarith only [h33836, h35719, hlam]
                            · linarith only [h33191, h35719, hlam]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [h33187, h33193, h34261, hc23, hc45, hlam, hphi, ht34, p35686_1]
                          · have p35686_0 := h35686c.1
                            have p35686_1 := h35686c.2.1
                            have p35686_2 := h35686c.2.2.1
                            have p35686_3 := h35686c.2.2.2
                            linarith only [hlam, p35686_0]
                  · linarith only [h34263, h35679, hlam]
                · linarith only [h35678, hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                rcases p35655_3 (m.d 0 2) (by simp) with h35726 | h35726
                · linarith only [h0, h35726, hlam]
                · rcases p35655_3 (m.d 1 2) (by simp) with h35728 | h35728
                  · rcases p35655_3 (m.d 2 3) (by simp) with h35729 | h35729
                    · linarith only [h34261, h35729, hlam]
                    · rcases p35655_3 (m.d 2 4) (by simp) with h35731 | h35731
                      · linarith only [h34262, h35731, hlam]
                      · rcases p35655_3 (m.d 2 5) (by simp) with h35733 | h35733
                        · linarith only [h34263, h35733, hlam]
                        · rcases h4bigk with h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c | h35735c
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [hlam, p35735_0]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h0, h33188, h34262, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35655_1, p35735_1]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35655_1, p35735_1]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h33193, hlam, p35735_1]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h33836, hlam, p35735_0]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h33188, hlam, p35735_0]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [hlam, p35735_0]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35655_1, p35735_1]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h34264, hlam, p35735_1]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h34268, hlam, p35735_0]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h33191, hlam, p35735_0]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h34262, hlam, p35735_0]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [hlam, p35735_0]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h34270, hlam, p35735_1]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h34274, hlam, p35735_0]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h34276, hc04, hc45, hlam, hphi, p35735_1]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h34276, hc14, hc45, hlam, hphi, p35735_1]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35735_1]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [hlam, p35735_0]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h34276, hlam, p35735_0]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            rcases p35735_3 (m.d 0 4) (by simp) with h35756 | h35756
                            · linarith only [h35756, hlam, p35735_0]
                            · rcases p35735_3 (m.d 1 4) (by simp) with h35758 | h35758
                              · linarith only [h34268, h35758, hlam]
                              · rcases p35735_3 (m.d 2 4) (by simp) with h35760 | h35760
                                · linarith only [h34274, h35760, hlam]
                                · rcases p35735_3 (m.d 3 4) (by simp) with h35762 | h35762
                                  · linarith only [h34276, h35762, hlam]
                                  · linarith only [h33193, h35762, hlam]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            rcases p35735_3 (m.d 0 4) (by simp) with h35765 | h35765
                            · linarith only [h33836, h35765, hlam]
                            · linarith only [h33188, h35765, hlam]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            rcases p35735_3 (m.d 0 4) (by simp) with h35768 | h35768
                            · linarith only [h33836, h35768, hlam]
                            · linarith only [h33191, h35768, hlam]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [h33187, h33193, h34261, hc23, hc45, hlam, hphi, ht34, p35735_1]
                          · have p35735_0 := h35735c.1
                            have p35735_1 := h35735c.2.1
                            have p35735_2 := h35735c.2.2.1
                            have p35735_3 := h35735c.2.2.2
                            linarith only [hlam, p35735_0]
                  · linarith only [h0, h35728, hlam]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h33187, h34261, hlam, p35197_1, p35655_2]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h33188, h34262, hlam, p35197_1, p35655_2]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h33189, h34263, hlam, p35197_1, p35655_2]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h33190, hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h34261, hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h34270, hlam, p35655_1]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h34272, hlam, p35655_1]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h33191, hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h34262, hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h33188, h34262, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35655_1]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h34274, hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h33192, hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h34263, hlam, p35655_0]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h33189, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35655_1]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [h33189, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p35197_1, p35655_1]
              · have p35655_0 := h35655c.1
                have p35655_1 := h35655c.2.1
                have p35655_2 := h35655c.2.2.1
                have p35655_3 := h35655c.2.2.2
                linarith only [hlam, p35655_0]
            · rcases h2bigk with h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c | h35793c
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h0, hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                rcases p35793_3 (m.d 0 2) (by simp) with h35796 | h35796
                · rcases p35793_3 (m.d 1 2) (by simp) with h35797 | h35797
                  · rcases p35793_3 (m.d 2 3) (by simp) with h35798 | h35798
                    · linarith only [h35798, hlam, p35793_0]
                    · rcases p35793_3 (m.d 2 4) (by simp) with h35800 | h35800
                      · linarith only [h33191, h35800, hlam]
                      · linarith only [h34270, h35800, hlam]
                  · linarith only [h34261, h35797, hlam]
                · linarith only [h35796, hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                rcases p35793_3 (m.d 0 2) (by simp) with h35805 | h35805
                · rcases p35793_3 (m.d 1 2) (by simp) with h35806 | h35806
                  · rcases p35793_3 (m.d 2 3) (by simp) with h35807 | h35807
                    · linarith only [h33190, h35807, hlam]
                    · rcases p35793_3 (m.d 2 4) (by simp) with h35809 | h35809
                      · linarith only [h35809, hlam, p35793_0]
                      · rcases p35793_3 (m.d 2 5) (by simp) with h35811 | h35811
                        · linarith only [h33192, h35811, hlam]
                        · linarith only [h34274, h35811, hlam]
                  · linarith only [h34262, h35806, hlam]
                · linarith only [h35805, hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                rcases p35793_3 (m.d 0 2) (by simp) with h35816 | h35816
                · rcases p35793_3 (m.d 1 2) (by simp) with h35817 | h35817
                  · rcases p35793_3 (m.d 2 3) (by simp) with h35818 | h35818
                    · linarith only [h33190, h35818, hlam]
                    · rcases p35793_3 (m.d 2 4) (by simp) with h35820 | h35820
                      · linarith only [h33191, h35820, hlam]
                      · rcases p35793_3 (m.d 2 5) (by simp) with h35822 | h35822
                        · linarith only [h35822, hlam, p35793_0]
                        · rcases h4bigk with h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c | h35824c
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [hlam, p35824_0]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h33188, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p35197_1, p35824_1]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35824_1]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h33193, hlam, p35824_1]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h33836, hlam, p35824_0]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h33188, hlam, p35824_0]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [hlam, p35824_0]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35824_1]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h34264, hlam, p35824_1]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h34268, hlam, p35824_0]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h33191, hlam, p35824_0]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h34262, hlam, p35824_0]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [hlam, p35824_0]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h34270, hlam, p35824_1]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h34274, hlam, p35824_0]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h33187, h33193, h34261, h34276, hc23, hc45, hlam, hphi, ht34, p35824_1]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35824_1]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35824_1]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [hlam, p35824_0]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h34276, hlam, p35824_0]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            rcases p35824_3 (m.d 0 4) (by simp) with h35845 | h35845
                            · linarith only [h35845, hlam, p35824_0]
                            · rcases p35824_3 (m.d 1 4) (by simp) with h35847 | h35847
                              · linarith only [h34268, h35847, hlam]
                              · rcases p35824_3 (m.d 2 4) (by simp) with h35849 | h35849
                                · linarith only [h34274, h35849, hlam]
                                · rcases p35824_3 (m.d 3 4) (by simp) with h35851 | h35851
                                  · linarith only [h34276, h35851, hlam]
                                  · linarith only [h33193, h35851, hlam]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            rcases p35824_3 (m.d 0 4) (by simp) with h35854 | h35854
                            · linarith only [h33836, h35854, hlam]
                            · linarith only [h33188, h35854, hlam]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            rcases p35824_3 (m.d 0 4) (by simp) with h35857 | h35857
                            · linarith only [h33836, h35857, hlam]
                            · linarith only [h33191, h35857, hlam]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [h33187, h33193, h34261, hc23, hc45, hlam, hphi, ht34, p35824_1]
                          · have p35824_0 := h35824c.1
                            have p35824_1 := h35824c.2.1
                            have p35824_2 := h35824c.2.2.1
                            have p35824_3 := h35824c.2.2.2
                            linarith only [hlam, p35824_0]
                  · linarith only [h34263, h35817, hlam]
                · linarith only [h35816, hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                rcases p35793_3 (m.d 0 2) (by simp) with h35864 | h35864
                · linarith only [h0, h35864, hlam]
                · rcases p35793_3 (m.d 1 2) (by simp) with h35866 | h35866
                  · rcases p35793_3 (m.d 2 3) (by simp) with h35867 | h35867
                    · linarith only [h34261, h35867, hlam]
                    · rcases p35793_3 (m.d 2 4) (by simp) with h35869 | h35869
                      · linarith only [h34262, h35869, hlam]
                      · rcases p35793_3 (m.d 2 5) (by simp) with h35871 | h35871
                        · linarith only [h34263, h35871, hlam]
                        · rcases h4bigk with h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c | h35873c
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [hlam, p35873_0]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h0, h33188, h34262, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35793_1, p35873_1]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35793_1, p35873_1]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h33193, hlam, p35873_1]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h33836, hlam, p35873_0]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h33188, hlam, p35873_0]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [hlam, p35873_0]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35793_1, p35873_1]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h34264, hlam, p35873_1]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h34268, hlam, p35873_0]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h33191, hlam, p35873_0]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h34262, hlam, p35873_0]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [hlam, p35873_0]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h34270, hlam, p35873_1]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h34274, hlam, p35873_0]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h33187, h33193, h34261, h34276, hc23, hc45, hlam, hphi, ht34, p35873_1]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35873_1]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35873_1]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [hlam, p35873_0]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h34276, hlam, p35873_0]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            rcases p35873_3 (m.d 0 4) (by simp) with h35894 | h35894
                            · linarith only [h35894, hlam, p35873_0]
                            · rcases p35873_3 (m.d 1 4) (by simp) with h35896 | h35896
                              · linarith only [h34268, h35896, hlam]
                              · rcases p35873_3 (m.d 2 4) (by simp) with h35898 | h35898
                                · linarith only [h34274, h35898, hlam]
                                · rcases p35873_3 (m.d 3 4) (by simp) with h35900 | h35900
                                  · linarith only [h34276, h35900, hlam]
                                  · linarith only [h33193, h35900, hlam]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            rcases p35873_3 (m.d 0 4) (by simp) with h35903 | h35903
                            · linarith only [h33836, h35903, hlam]
                            · linarith only [h33188, h35903, hlam]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            rcases p35873_3 (m.d 0 4) (by simp) with h35906 | h35906
                            · linarith only [h33836, h35906, hlam]
                            · linarith only [h33191, h35906, hlam]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [h33187, h33193, h34261, hc23, hc45, hlam, hphi, ht34, p35873_1]
                          · have p35873_0 := h35873c.1
                            have p35873_1 := h35873c.2.1
                            have p35873_2 := h35873c.2.2.1
                            have p35873_3 := h35873c.2.2.2
                            linarith only [hlam, p35873_0]
                  · linarith only [h0, h35866, hlam]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h33187, h34261, hlam, p35197_1, p35793_2]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h33188, h34262, hlam, p35197_1, p35793_2]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h33189, h34263, hlam, p35197_1, p35793_2]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h33190, hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h34261, hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h34270, hlam, p35793_1]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h34272, hlam, p35793_1]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h33191, hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h34262, hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h33188, h34262, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35793_1]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h34274, hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h33192, hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h34263, hlam, p35793_0]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h33189, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35793_1]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [h33189, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p35197_1, p35793_1]
              · have p35793_0 := h35793c.1
                have p35793_1 := h35793c.2.1
                have p35793_2 := h35793c.2.2.1
                have p35793_3 := h35793c.2.2.2
                linarith only [hlam, p35793_0]
            · rcases h2bigk with h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c | h35931c
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h0, hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                rcases p35931_3 (m.d 0 2) (by simp) with h35934 | h35934
                · rcases p35931_3 (m.d 1 2) (by simp) with h35935 | h35935
                  · rcases p35931_3 (m.d 2 3) (by simp) with h35936 | h35936
                    · linarith only [h35936, hlam, p35931_0]
                    · rcases p35931_3 (m.d 2 4) (by simp) with h35938 | h35938
                      · linarith only [h33191, h35938, hlam]
                      · linarith only [h34270, h35938, hlam]
                  · linarith only [h34261, h35935, hlam]
                · linarith only [h35934, hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                rcases p35931_3 (m.d 0 2) (by simp) with h35943 | h35943
                · rcases p35931_3 (m.d 1 2) (by simp) with h35944 | h35944
                  · rcases p35931_3 (m.d 2 3) (by simp) with h35945 | h35945
                    · linarith only [h33190, h35945, hlam]
                    · rcases p35931_3 (m.d 2 4) (by simp) with h35947 | h35947
                      · linarith only [h35947, hlam, p35931_0]
                      · rcases p35931_3 (m.d 2 5) (by simp) with h35949 | h35949
                        · linarith only [h33192, h35949, hlam]
                        · linarith only [h34274, h35949, hlam]
                  · linarith only [h34262, h35944, hlam]
                · linarith only [h35943, hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                rcases p35931_3 (m.d 0 2) (by simp) with h35954 | h35954
                · rcases p35931_3 (m.d 1 2) (by simp) with h35955 | h35955
                  · rcases p35931_3 (m.d 2 3) (by simp) with h35956 | h35956
                    · linarith only [h33190, h35956, hlam]
                    · rcases p35931_3 (m.d 2 4) (by simp) with h35958 | h35958
                      · linarith only [h33191, h35958, hlam]
                      · rcases p35931_3 (m.d 2 5) (by simp) with h35960 | h35960
                        · linarith only [h35960, hlam, p35931_0]
                        · rcases h4bigk with h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c | h35962c
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [hlam, p35962_0]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h33188, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p35197_1, p35962_1]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35962_1]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h33193, hlam, p35962_1]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h33836, hlam, p35962_0]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h33188, hlam, p35962_0]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [hlam, p35962_0]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35962_1]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h34264, hlam, p35962_1]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h34268, hlam, p35962_0]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h33191, hlam, p35962_0]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h34262, hlam, p35962_0]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [hlam, p35962_0]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h34270, hlam, p35962_1]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h34274, hlam, p35962_0]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h33187, h33193, h34261, h34276, hc23, hc45, hlam, hphi, ht34, p35962_1]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h34262, h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35962_1]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h34270, h34276, hc23, hc45, hlam, hphi, ht34, p35962_1]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [hlam, p35962_0]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h34276, hlam, p35962_0]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            rcases p35962_3 (m.d 0 4) (by simp) with h35983 | h35983
                            · linarith only [h35983, hlam, p35962_0]
                            · rcases p35962_3 (m.d 1 4) (by simp) with h35985 | h35985
                              · linarith only [h34268, h35985, hlam]
                              · rcases p35962_3 (m.d 2 4) (by simp) with h35987 | h35987
                                · linarith only [h34274, h35987, hlam]
                                · rcases p35962_3 (m.d 3 4) (by simp) with h35989 | h35989
                                  · linarith only [h34276, h35989, hlam]
                                  · linarith only [h33193, h35989, hlam]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            rcases p35962_3 (m.d 0 4) (by simp) with h35992 | h35992
                            · linarith only [h33836, h35992, hlam]
                            · linarith only [h33188, h35992, hlam]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            rcases p35962_3 (m.d 0 4) (by simp) with h35995 | h35995
                            · linarith only [h33836, h35995, hlam]
                            · linarith only [h33191, h35995, hlam]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [h33187, h33193, h34261, hc23, hc45, hlam, hphi, ht34, p35962_1]
                          · have p35962_0 := h35962c.1
                            have p35962_1 := h35962c.2.1
                            have p35962_2 := h35962c.2.2.1
                            have p35962_3 := h35962c.2.2.2
                            linarith only [hlam, p35962_0]
                  · linarith only [h34263, h35955, hlam]
                · linarith only [h35954, hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                rcases p35931_3 (m.d 0 2) (by simp) with h36002 | h36002
                · linarith only [h0, h36002, hlam]
                · rcases p35931_3 (m.d 1 2) (by simp) with h36004 | h36004
                  · rcases p35931_3 (m.d 2 3) (by simp) with h36005 | h36005
                    · linarith only [h34261, h36005, hlam]
                    · rcases p35931_3 (m.d 2 4) (by simp) with h36007 | h36007
                      · linarith only [h34262, h36007, hlam]
                      · rcases p35931_3 (m.d 2 5) (by simp) with h36009 | h36009
                        · linarith only [h34263, h36009, hlam]
                        · rcases h4bigk with h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c | h36011c
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [hlam, p36011_0]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h0, h33188, h34262, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35931_1, p36011_1]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35931_1, p36011_1]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h33193, hlam, p36011_1]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h33836, hlam, p36011_0]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h33188, hlam, p36011_0]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [hlam, p36011_0]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h0, h33188, h34270, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35931_1, p36011_1]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h34264, hlam, p36011_1]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h34268, hlam, p36011_0]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h33191, hlam, p36011_0]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h34262, hlam, p36011_0]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [hlam, p36011_0]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h34270, hlam, p36011_1]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h34274, hlam, p36011_0]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h34276, hc04, hc45, hlam, hphi, p36011_1]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h34276, hc14, hc45, hlam, hphi, p36011_1]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h34270, h34276, hc23, hc45, hlam, hphi, ht34, p36011_1]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [hlam, p36011_0]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h34276, hlam, p36011_0]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            rcases p36011_3 (m.d 0 4) (by simp) with h36032 | h36032
                            · linarith only [h36032, hlam, p36011_0]
                            · rcases p36011_3 (m.d 1 4) (by simp) with h36034 | h36034
                              · linarith only [h34268, h36034, hlam]
                              · rcases p36011_3 (m.d 2 4) (by simp) with h36036 | h36036
                                · linarith only [h34274, h36036, hlam]
                                · rcases p36011_3 (m.d 3 4) (by simp) with h36038 | h36038
                                  · linarith only [h34276, h36038, hlam]
                                  · linarith only [h33193, h36038, hlam]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            rcases p36011_3 (m.d 0 4) (by simp) with h36041 | h36041
                            · linarith only [h33836, h36041, hlam]
                            · linarith only [h33188, h36041, hlam]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            rcases p36011_3 (m.d 0 4) (by simp) with h36044 | h36044
                            · linarith only [h33836, h36044, hlam]
                            · linarith only [h33191, h36044, hlam]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [h33187, h33193, h34261, hc23, hc45, hlam, hphi, ht34, p36011_1]
                          · have p36011_0 := h36011c.1
                            have p36011_1 := h36011c.2.1
                            have p36011_2 := h36011c.2.2.1
                            have p36011_3 := h36011c.2.2.2
                            linarith only [hlam, p36011_0]
                  · linarith only [h0, h36004, hlam]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h33187, h34261, hlam, p35197_1, p35931_2]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h33188, h34262, hlam, p35197_1, p35931_2]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h33189, h34263, hlam, p35197_1, p35931_2]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h33190, hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h34261, hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h34270, hlam, p35931_1]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h34272, hlam, p35931_1]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h33191, hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h34262, hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h33188, h34262, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35931_1]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h34274, hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h33192, hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h34263, hlam, p35931_0]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h33189, h34263, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p35197_1, p35931_1]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [h33189, h34263, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p35197_1, p35931_1]
              · have p35931_0 := h35931c.1
                have p35931_1 := h35931c.2.1
                have p35931_2 := h35931c.2.2.1
                have p35931_3 := h35931c.2.2.2
                linarith only [hlam, p35931_0]
    · linarith only [h35508, hlam, p35197_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 1 2) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 2) ∧ (m.d 1 2) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 2) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  linarith only [hlam, p35197_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 1 2) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 2) ∧ (m.d 1 3) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 3) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  rcases p35197_3 (m.d 0 1) (by simp) with h36071 | h36071
  · linarith only [h0, h36071, hlam]
  · linarith only [h33187, h36071, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x8 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 1 2) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 2) ∧ (m.d 1 4) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 4) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  rcases p35197_3 (m.d 0 1) (by simp) with h36074 | h36074
  · linarith only [h0, h36074, hlam]
  · linarith only [h33188, h36074, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x9 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 1 2) < (m.d 1 5) ∧ 2 * m.lam ≤ (m.d 1 5) - (m.d 1 2) ∧ (m.d 1 5) - (m.d 1 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 2) ∨ (m.d 1 5) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  rcases p35197_3 (m.d 0 1) (by simp) with h36077 | h36077
  · linarith only [h0, h36077, hlam]
  · linarith only [h33189, h36077, hlam]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 1 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 1 3) ∧ (m.d 0 1) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 0 1) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  linarith only [h33187, hlam, p35197_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 1 3) < (m.d 1 2) ∧ 2 * m.lam ≤ (m.d 1 2) - (m.d 1 3) ∧ (m.d 1 2) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 2) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  linarith only [h34261, hlam, p35197_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 1 3) < (m.d 1 3) ∧ 2 * m.lam ≤ (m.d 1 3) - (m.d 1 3) ∧ (m.d 1 3) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 3) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  linarith only [hlam, p35197_0]

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s36_x1_x1_x1_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x13 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg33188 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg33189 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg33190 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg33191 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg33192 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h33193 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h33775 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h33836 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h34261 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h34262 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h34263 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h34264 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h34266 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h34268 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h34270 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h34272 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h34274 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h34276 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h35197c : ((m.d 1 3) < (m.d 1 4) ∧ 2 * m.lam ≤ (m.d 1 4) - (m.d 1 3) ∧ (m.d 1 4) - (m.d 1 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 1 3) ∨ (m.d 1 4) ≤ z)))
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
  have h33187 := hg33187
  have h33188 := hg33188
  have h33189 := hg33189
  have h33190 := hg33190
  have h33191 := hg33191
  have h33192 := hg33192
  have p35197_0 := h35197c.1
  have p35197_1 := h35197c.2.1
  have p35197_2 := h35197c.2.2.1
  have p35197_3 := h35197c.2.2.2
  linarith only [h34264, hlam, p35197_0]

end R2N4
