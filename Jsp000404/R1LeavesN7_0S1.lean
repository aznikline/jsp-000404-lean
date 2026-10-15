import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x0 (m : N7Model)
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
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  rcases m.htr 2 3 4 (by decide) (by decide) with h499 | h499
  · linarith only [h0, h10, h13, h499, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h501 | h501
    · linarith only [h10, h437, h501, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h503 | h503
      · rcases m.htr 3 4 5 (by decide) (by decide) with h504 | h504
        · rcases h1bigk with h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c | h505c
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h11, h503, hc01, hc45, hlam, hphi, ht0b, ht5b, p505_1]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            rcases p505_3 (m.d 0 1) (by simp) with h508 | h508
            · rcases p505_3 (m.d 1 2) (by simp) with h509 | h509
              · linarith only [h0, h509, hlam]
              · linarith only [h10, h509, hlam]
            · linarith only [h508, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            rcases p505_3 (m.d 0 1) (by simp) with h513 | h513
            · rcases p505_3 (m.d 1 2) (by simp) with h514 | h514
              · linarith only [h0, h514, hlam]
              · linarith only [h11, h514, hlam]
            · linarith only [h513, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            rcases p505_3 (m.d 0 1) (by simp) with h518 | h518
            · rcases p505_3 (m.d 1 2) (by simp) with h519 | h519
              · linarith only [h0, h519, hlam]
              · linarith only [h12, h519, hlam]
            · linarith only [h518, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h0, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            rcases p505_3 (m.d 0 1) (by simp) with h525 | h525
            · rcases p505_3 (m.d 1 2) (by simp) with h526 | h526
              · rcases p505_3 (m.d 1 3) (by simp) with h527 | h527
                · linarith only [h10, h527, hlam]
                · rcases p505_3 (m.d 1 4) (by simp) with h529 | h529
                  · linarith only [h11, h529, hlam]
                  · linarith only [h13, h529, hlam]
              · linarith only [h10, h526, hlam]
            · linarith only [h1, h525, hlam]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h0, h11, h503, hc01, hc45, hlam, hphi, ht0b, ht5b, p505_1]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            rcases p505_3 (m.d 0 1) (by simp) with h535 | h535
            · rcases p505_3 (m.d 1 2) (by simp) with h536 | h536
              · rcases p505_3 (m.d 1 3) (by simp) with h537 | h537
                · linarith only [h10, h537, hlam]
                · rcases p505_3 (m.d 1 4) (by simp) with h539 | h539
                  · linarith only [h11, h539, hlam]
                  · linarith only [h498, h539, hlam]
              · linarith only [h12, h536, hlam]
            · linarith only [h3, h535, hlam]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h1, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h10, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h13, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h437, hlam, p505_1]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h2, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h11, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            rcases p505_3 (m.d 0 1) (by simp) with h551 | h551
            · rcases p505_3 (m.d 1 2) (by simp) with h552 | h552
              · rcases p505_3 (m.d 1 3) (by simp) with h553 | h553
                · linarith only [h13, h553, hlam]
                · rcases p505_3 (m.d 1 4) (by simp) with h555 | h555
                  · rcases p505_3 (m.d 1 5) (by simp) with h556 | h556
                    · linarith only [h498, h556, hlam]
                    · linarith only [h437, h556, hlam]
                  · linarith only [h13, h555, hlam]
              · linarith only [h10, h552, hlam]
            · linarith only [h1, h551, hlam]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            rcases p505_3 (m.d 0 1) (by simp) with h563 | h563
            · rcases p505_3 (m.d 1 2) (by simp) with h564 | h564
              · rcases p505_3 (m.d 1 3) (by simp) with h565 | h565
                · linarith only [h13, h565, hlam]
                · rcases p505_3 (m.d 1 4) (by simp) with h567 | h567
                  · rcases p505_3 (m.d 1 5) (by simp) with h568 | h568
                    · linarith only [h498, h568, hlam]
                    · rcases h1emax with h570 | h570 | h570 | h570 | h570
                      · linarith only [h0, h13, h4, h437, h570, h7, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p505_1]
                      · linarith only [h11, h503, h570, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases h2bigk with h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [hlam, p573_0]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h0, h10, h11, h437, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p505_1, p573_1]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h10, h13, h4, h437, h7, hlam, p505_1, p573_2]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          rcases p573_3 (m.d 0 2) (by simp) with h577 | h577
                          · rcases p573_3 (m.d 1 2) (by simp) with h578 | h578
                            · linarith only [h0, h578, hlam]
                            · linarith only [h11, h578, hlam]
                          · linarith only [h577, hlam, p573_0]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h12, h13, h4, h7, hlam, p505_1, p573_2]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h0, hlam, p573_1]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [hlam, p573_0]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          rcases p573_3 (m.d 0 2) (by simp) with h585 | h585
                          · rcases p573_3 (m.d 1 2) (by simp) with h586 | h586
                            · rcases p573_3 (m.d 2 3) (by simp) with h587 | h587
                              · linarith only [h587, hlam, p573_0]
                              · rcases p573_3 (m.d 2 4) (by simp) with h589 | h589
                                · linarith only [h11, h589, hlam]
                                · linarith only [h499, h589, hlam]
                            · linarith only [h586, hlam, p573_0]
                          · linarith only [h4, h585, hlam]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h0, h503, hc01, hc45, hlam, hphi, ht0b, ht5b, p573_1]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          rcases p573_3 (m.d 0 2) (by simp) with h595 | h595
                          · rcases p573_3 (m.d 1 2) (by simp) with h596 | h596
                            · rcases p573_3 (m.d 2 3) (by simp) with h597 | h597
                              · linarith only [h10, h597, hlam]
                              · rcases p573_3 (m.d 2 4) (by simp) with h599 | h599
                                · linarith only [h11, h599, hlam]
                                · linarith only [h503, h599, hlam]
                            · linarith only [h596, hlam, p573_0]
                          · linarith only [h595, h6, hlam]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h4, hlam, p573_0]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h10, hlam, p573_0]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [hlam, p573_0]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h499, hlam, p573_1]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h501, hlam, p573_1]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h5, hlam, p573_0]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h11, hlam, p573_0]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p573_1]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [hlam, p573_0]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h0, h11, hc01, hc25, hlam, hphi, ht0b, ht5b, p573_1]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h6, hlam, p573_0]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h12, hlam, p573_0]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p573_1]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [h503, hlam, p573_1]
                        · have p573_0 := h573c.1
                          have p573_1 := h573c.2.1
                          have p573_2 := h573c.2.2.1
                          have p573_3 := h573c.2.2.2
                          linarith only [hlam, p573_0]
                      · linarith only [h10, h437, h570, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p505_1]
                      · rcases h2bigk with h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c | h620c
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [hlam, p620_0]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h0, h10, h11, h437, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p505_1, p620_1]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h10, h13, h4, h437, h7, hlam, p505_1, p620_2]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          rcases p620_3 (m.d 0 2) (by simp) with h624 | h624
                          · rcases p620_3 (m.d 1 2) (by simp) with h625 | h625
                            · linarith only [h0, h625, hlam]
                            · linarith only [h11, h625, hlam]
                          · linarith only [h624, hlam, p620_0]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h12, h13, h4, h7, hlam, p505_1, p620_2]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h0, hlam, p620_1]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [hlam, p620_0]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          rcases p620_3 (m.d 0 2) (by simp) with h632 | h632
                          · rcases p620_3 (m.d 1 2) (by simp) with h633 | h633
                            · rcases p620_3 (m.d 2 3) (by simp) with h634 | h634
                              · linarith only [h634, hlam, p620_0]
                              · rcases p620_3 (m.d 2 4) (by simp) with h636 | h636
                                · linarith only [h11, h636, hlam]
                                · linarith only [h499, h636, hlam]
                            · linarith only [h633, hlam, p620_0]
                          · linarith only [h4, h632, hlam]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h0, h503, hc01, hc45, hlam, hphi, ht0b, ht5b, p620_1]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          rcases p620_3 (m.d 0 2) (by simp) with h642 | h642
                          · rcases p620_3 (m.d 1 2) (by simp) with h643 | h643
                            · rcases p620_3 (m.d 2 3) (by simp) with h644 | h644
                              · linarith only [h10, h644, hlam]
                              · rcases p620_3 (m.d 2 4) (by simp) with h646 | h646
                                · linarith only [h11, h646, hlam]
                                · linarith only [h503, h646, hlam]
                            · linarith only [h643, hlam, p620_0]
                          · linarith only [h6, h642, hlam]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h4, hlam, p620_0]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h10, hlam, p620_0]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [hlam, p620_0]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h499, hlam, p620_1]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h501, hlam, p620_1]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h5, hlam, p620_0]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h11, hlam, p620_0]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p620_1]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [hlam, p620_0]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h0, h11, hc01, hc25, hlam, hphi, ht0b, ht5b, p620_1]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h6, hlam, p620_0]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h12, hlam, p620_0]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p620_1]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [h503, hlam, p620_1]
                        · have p620_0 := h620c.1
                          have p620_1 := h620c.2.1
                          have p620_2 := h620c.2.2.1
                          have p620_3 := h620c.2.2.2
                          linarith only [hlam, p620_0]
                  · linarith only [h498, h567, hlam]
              · linarith only [h12, h564, hlam]
            · linarith only [h3, h563, hlam]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h3, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h12, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            rcases p505_3 (m.d 0 1) (by simp) with h671 | h671
            · rcases p505_3 (m.d 1 2) (by simp) with h672 | h672
              · rcases p505_3 (m.d 1 3) (by simp) with h673 | h673
                · linarith only [h437, h673, hlam]
                · rcases p505_3 (m.d 1 4) (by simp) with h675 | h675
                  · rcases p505_3 (m.d 1 5) (by simp) with h676 | h676
                    · rcases h1emax with h677 | h677 | h677 | h677 | h677
                      · linarith only [h0, h11, h677, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h10, h11, h498, h677, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p505_1]
                      · rcases h2bigk with h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c | h680c
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h0, h10, h11, h498, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p505_1, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h10, h4, h437, h504, h7, hlam, p505_1, p680_2]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          rcases p680_3 (m.d 0 2) (by simp) with h684 | h684
                          · rcases p680_3 (m.d 1 2) (by simp) with h685 | h685
                            · linarith only [h0, h685, hlam]
                            · linarith only [h11, h685, hlam]
                          · linarith only [h684, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          rcases p680_3 (m.d 0 2) (by simp) with h689 | h689
                          · rcases p680_3 (m.d 1 2) (by simp) with h690 | h690
                            · linarith only [h0, h690, hlam]
                            · linarith only [h12, h690, hlam]
                          · linarith only [h689, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h0, hlam, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          rcases p680_3 (m.d 0 2) (by simp) with h696 | h696
                          · rcases p680_3 (m.d 1 2) (by simp) with h697 | h697
                            · rcases p680_3 (m.d 2 3) (by simp) with h698 | h698
                              · linarith only [h698, hlam, p680_0]
                              · rcases p680_3 (m.d 2 4) (by simp) with h700 | h700
                                · linarith only [h11, h700, hlam]
                                · linarith only [h499, h700, hlam]
                            · linarith only [h697, hlam, p680_0]
                          · linarith only [h4, h696, hlam]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h0, h503, hc01, hc45, hlam, hphi, ht0b, ht5b, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          rcases p680_3 (m.d 0 2) (by simp) with h706 | h706
                          · rcases p680_3 (m.d 1 2) (by simp) with h707 | h707
                            · rcases p680_3 (m.d 2 3) (by simp) with h708 | h708
                              · linarith only [h10, h708, hlam]
                              · rcases p680_3 (m.d 2 4) (by simp) with h710 | h710
                                · linarith only [h11, h710, hlam]
                                · linarith only [h503, h710, hlam]
                            · linarith only [h707, hlam, p680_0]
                          · linarith only [h6, h706, hlam]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h4, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h10, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h499, hlam, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h501, hlam, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h5, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h11, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h0, h11, hc01, hc25, hlam, hphi, ht0b, ht5b, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h6, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h12, hlam, p680_0]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [h503, hlam, p680_1]
                        · have p680_0 := h680c.1
                          have p680_1 := h680c.2.1
                          have p680_2 := h680c.2.2.1
                          have p680_3 := h680c.2.2.2
                          linarith only [hlam, p680_0]
                      · linarith only [h10, h498, h677, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p505_1]
                      · linarith only [h10, h677, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p505_1]
                    · linarith only [h437, h676, hlam]
                  · linarith only [h13, h675, hlam]
              · linarith only [h10, h672, hlam]
            · linarith only [h1, h671, hlam]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [h498, hlam, p505_0]
          · have p505_0 := h505c.1
            have p505_1 := h505c.2.1
            have p505_2 := h505c.2.2.1
            have p505_3 := h505c.2.2.2
            linarith only [hlam, p505_0]
        · linarith only [h13, h498, h504, hlam]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h739 | h739
        · rcases h1bigk with h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c | h740c
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h11, h498, h503, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p740_1]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            rcases p740_3 (m.d 0 1) (by simp) with h743 | h743
            · rcases p740_3 (m.d 1 2) (by simp) with h744 | h744
              · linarith only [h0, h744, hlam]
              · linarith only [h10, h744, hlam]
            · linarith only [h743, hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h498, h499, h503, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p740_1]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            rcases p740_3 (m.d 0 1) (by simp) with h749 | h749
            · rcases p740_3 (m.d 1 2) (by simp) with h750 | h750
              · linarith only [h0, h750, hlam]
              · linarith only [h12, h750, hlam]
            · linarith only [h749, hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h0, hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            rcases p740_3 (m.d 0 1) (by simp) with h756 | h756
            · rcases p740_3 (m.d 1 2) (by simp) with h757 | h757
              · rcases p740_3 (m.d 1 3) (by simp) with h758 | h758
                · linarith only [h10, h758, hlam]
                · rcases p740_3 (m.d 1 4) (by simp) with h760 | h760
                  · linarith only [h11, h760, hlam]
                  · linarith only [h13, h760, hlam]
              · linarith only [h10, h757, hlam]
            · linarith only [h1, h756, hlam]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h498, h499, h503, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p740_1]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h0, h498, h499, h503, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p740_1]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h1, hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h10, hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h13, hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h437, hlam, p740_1]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h2, hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h11, hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            rcases p740_3 (m.d 0 1) (by simp) with h774 | h774
            · rcases p740_3 (m.d 1 2) (by simp) with h775 | h775
              · rcases p740_3 (m.d 1 3) (by simp) with h776 | h776
                · linarith only [h13, h776, hlam]
                · rcases p740_3 (m.d 1 4) (by simp) with h778 | h778
                  · rcases p740_3 (m.d 1 5) (by simp) with h779 | h779
                    · linarith only [h498, h779, hlam]
                    · linarith only [h437, h779, hlam]
                  · linarith only [h13, h778, hlam]
              · linarith only [h10, h775, hlam]
            · linarith only [h1, h774, hlam]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h2, h498, h499, h503, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p740_1]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h3, hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h12, hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            rcases p740_3 (m.d 0 1) (by simp) with h789 | h789
            · rcases p740_3 (m.d 1 2) (by simp) with h790 | h790
              · rcases p740_3 (m.d 1 3) (by simp) with h791 | h791
                · linarith only [h437, h791, hlam]
                · rcases p740_3 (m.d 1 4) (by simp) with h793 | h793
                  · rcases p740_3 (m.d 1 5) (by simp) with h794 | h794
                    · rcases h1emax with h795 | h795 | h795 | h795 | h795
                      · linarith only [h0, h4, h437, h7, h739, h795, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p740_1]
                      · linarith only [h10, h12, h795, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p740_1]
                      · rcases h2bigk with h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c | h798c
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h0, h10, h11, h498, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p740_1, p798_1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h10, h4, h437, h7, h739, hlam, p740_1, p798_2]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h13, h4, h498, h503, h7, hlam, p798_2]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          rcases p798_3 (m.d 0 2) (by simp) with h803 | h803
                          · rcases p798_3 (m.d 1 2) (by simp) with h804 | h804
                            · linarith only [h0, h804, hlam]
                            · linarith only [h12, h804, hlam]
                          · linarith only [h803, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h0, hlam, p798_1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          rcases p798_3 (m.d 0 2) (by simp) with h810 | h810
                          · rcases p798_3 (m.d 1 2) (by simp) with h811 | h811
                            · rcases p798_3 (m.d 2 3) (by simp) with h812 | h812
                              · linarith only [h812, hlam, p798_0]
                              · rcases p798_3 (m.d 2 4) (by simp) with h814 | h814
                                · linarith only [h11, h814, hlam]
                                · linarith only [h499, h814, hlam]
                            · linarith only [h811, hlam, p798_0]
                          · linarith only [h4, h810, hlam]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          rcases p798_3 (m.d 0 2) (by simp) with h819 | h819
                          · rcases p798_3 (m.d 1 2) (by simp) with h820 | h820
                            · rcases p798_3 (m.d 2 3) (by simp) with h821 | h821
                              · linarith only [h10, h821, hlam]
                              · rcases p798_3 (m.d 2 4) (by simp) with h823 | h823
                                · linarith only [h823, hlam, p798_0]
                                · rcases p798_3 (m.d 2 5) (by simp) with h825 | h825
                                  · linarith only [h12, h825, hlam]
                                  · linarith only [h503, h825, hlam]
                            · linarith only [h820, hlam, p798_0]
                          · linarith only [h5, h819, hlam]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          rcases p798_3 (m.d 0 2) (by simp) with h830 | h830
                          · rcases p798_3 (m.d 1 2) (by simp) with h831 | h831
                            · rcases p798_3 (m.d 2 3) (by simp) with h832 | h832
                              · linarith only [h10, h832, hlam]
                              · rcases p798_3 (m.d 2 4) (by simp) with h834 | h834
                                · linarith only [h11, h834, hlam]
                                · rcases p798_3 (m.d 2 5) (by simp) with h836 | h836
                                  · linarith only [h836, hlam, p798_0]
                                  · rcases h4bigk with h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c | h838c
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h4, h498, h503, h7, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p838_1]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      rcases p838_3 (m.d 0 4) (by simp) with h841 | h841
                                      · rcases p838_3 (m.d 1 4) (by simp) with h842 | h842
                                        · linarith only [h2, h842, hlam]
                                        · linarith only [h11, h842, hlam]
                                      · linarith only [h5, h841, hlam]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h10, h437, h739, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p740_1, p838_1]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      rcases p838_3 (m.d 0 4) (by simp) with h847 | h847
                                      · rcases p838_3 (m.d 1 4) (by simp) with h848 | h848
                                        · linarith only [h2, h848, hlam]
                                        · linarith only [h498, h848, hlam]
                                      · linarith only [h847, hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h2, hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      rcases p838_3 (m.d 0 4) (by simp) with h854 | h854
                                      · rcases p838_3 (m.d 1 4) (by simp) with h855 | h855
                                        · rcases p838_3 (m.d 2 4) (by simp) with h856 | h856
                                          · linarith only [h11, h856, hlam]
                                          · rcases p838_3 (m.d 3 4) (by simp) with h858 | h858
                                            · rcases p838_3 (m.d 4 5) (by simp) with h859 | h859
                                              · linarith only [h498, h859, hlam]
                                              · linarith only [h503, h859, hlam]
                                            · linarith only [h499, h858, hlam]
                                        · linarith only [h11, h855, hlam]
                                      · linarith only [h5, h854, hlam]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h13, hlam, p838_1]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h2, h499, h503, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p838_1]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h5, hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h11, hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h499, hlam, p838_1]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h503, hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h7, hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h498, h499, h503, hc23, hc34, hlam, hphi, p838_1]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      rcases p838_3 (m.d 0 4) (by simp) with h874 | h874
                                      · rcases p838_3 (m.d 1 4) (by simp) with h875 | h875
                                        · linarith only [h13, h875, hlam]
                                        · linarith only [h11, h875, hlam]
                                      · linarith only [h5, h874, hlam]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h0, h4, h499, h503, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p838_1]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h9, hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h498, hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h2, h498, h499, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p838_1]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [h739, hlam, p838_0]
                                    · have p838_0 := h838c.1
                                      have p838_1 := h838c.2.1
                                      have p838_2 := h838c.2.2.1
                                      have p838_3 := h838c.2.2.2
                                      linarith only [hlam, p838_0]
                            · linarith only [h831, hlam, p798_0]
                          · linarith only [h6, h830, hlam]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h4, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h10, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h499, hlam, p798_1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h501, hlam, p798_1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h5, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h11, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h0, h11, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p798_1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h503, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h6, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h12, hlam, p798_0]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h0, h12, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p798_1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [h0, h13, h4, h498, h503, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p798_1]
                        · have p798_0 := h798c.1
                          have p798_1 := h798c.2.1
                          have p798_2 := h798c.2.2.1
                          have p798_3 := h798c.2.2.2
                          linarith only [hlam, p798_0]
                      · linarith only [h10, h498, h795, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p740_1]
                      · linarith only [h10, h795, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p740_1]
                    · linarith only [h437, h794, hlam]
                  · linarith only [h13, h793, hlam]
              · linarith only [h10, h790, hlam]
            · linarith only [h1, h789, hlam]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [h498, hlam, p740_0]
          · have p740_0 := h740c.1
            have p740_1 := h740c.2.1
            have p740_2 := h740c.2.2.1
            have p740_3 := h740c.2.2.2
            linarith only [hlam, p740_0]
        · linarith only [h10, h13, h2, h498, h739, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x0 (m : N7Model)
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
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  linarith only [h10, h13, h912, hlam]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x0 (m : N7Model)
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
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  linarith only [h10, h437, h914, hlam]

set_option maxHeartbeats 5610000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s12_x1_x1_x1_x1_x1_x0 (m : N7Model)
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
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h437 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h498 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h912 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h914 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h916 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h10 := hg10
  have h11 := hg11
  have h12 := hg12
  linarith only [h0, h11, h498, h916, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]

end R2N4
