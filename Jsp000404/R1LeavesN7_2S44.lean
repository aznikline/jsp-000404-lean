import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S40
import Jsp000404.R1LeavesN7_2S41
import Jsp000404.R1LeavesN7_2S42
import Jsp000404.R1LeavesN7_2S43

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16662000 in
set_option maxHeartbeats 16662000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h20408 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h26804 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h27373 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h27730 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  rcases m.htr 0 3 5 (by decide) (by decide) with h28466 | h28466
  · rcases m.htr 0 4 5 (by decide) (by decide) with h28467 | h28467
    · rcases m.htr 1 2 3 (by decide) (by decide) with h28468 | h28468
      · rcases m.htr 1 2 4 (by decide) (by decide) with h28469 | h28469
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28470 | h28470
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28471 | h28471
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28472 | h28472
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28473 | h28473
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28474 | h28474
                  · linarith only [h27730, h28466, h28468, h28474, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h20408, h28468, h28471, h28474, hc01, hc12, hlam, hphi]
                · linarith only [h16915, h27373, h28467, h28470, h28473, hc01, hc12, hlam, hphi]
              · linarith only [h27730, h28471, h28472, hc03, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28479 | h28479
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28480 | h28480
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28481 | h28481
                  · linarith only [h28468, h28471, h28481, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28483 | h28483
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28484 | h28484
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28485 | h28485
                        · rcases h0bigk with h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c | h28486c
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [hlam, p28486_0]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h0, hlam, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h14396, hlam, p28486_0]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h16915, hlam, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h18815, hlam, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h27373, h28483, hc01, hc23, hlam, hphi, ht12, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [hlam, p28486_0]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h20408, hlam, p28486_0]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h26804, hlam, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h27373, hlam, p28486_0]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h14396, h28471, hc01, hc34, hlam, hphi, ht12, ht23, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h14396, h28471, hc02, hc34, hlam, hphi, ht23, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [hlam, p28486_0]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h27730, hlam, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h14396, h18815, h28471, hc01, hc34, hlam, hphi, ht12, ht23, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h26804, h28469, hc01, hc12, hlam, hphi, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h0, h26804, h28469, hc01, hc12, hlam, hphi, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h26804, h28466, h28469, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [hlam, p28486_0]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h0, h26804, h27373, h28469, hc01, hc12, hlam, hphi, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h18815, h28471, h28479, hc01, hc34, hlam, hphi, ht12, ht23, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h0, h27373, h28468, h28471, h28483, hc01, hc34, hlam, hphi, ht12, ht23, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h28466, hlam, p28486_0]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [h28467, hlam, p28486_1]
                          · have p28486_0 := h28486c.1
                            have p28486_1 := h28486c.2.1
                            have p28486_2 := h28486c.2.2.1
                            have p28486_3 := h28486c.2.2.2
                            linarith only [hlam, p28486_0]
                        · linarith only [h14396, h28471, h28485, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h26804, h28467, h28484, hlam]
                    · linarith only [h20408, h28466, h28483, hlam]
                · linarith only [h26804, h28467, h28469, h28480, hlam]
              · linarith only [h14396, h20408, h28466, h28479, hc01, hc23, hlam, hphi, ht12]
          · linarith only [h0, h20408, h28468, h28470, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h20408, h28468, h28469, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h28519 | h28519
        · linarith only [h0, h26804, h28468, h28519, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28521 | h28521
          · linarith only [h0, h27373, h28468, h28521, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28523 | h28523
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28524 | h28524
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28525 | h28525
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28526 | h28526
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28527 | h28527
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28528 | h28528
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28529 | h28529
                        · rcases h0bigk with h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c | h28530c
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [hlam, p28530_0]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h0, hlam, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h14396, hlam, p28530_0]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h16915, hlam, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h18815, hlam, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h27373, h27730, h28466, hc01, hc34, hlam, hphi, ht12, ht23, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [hlam, p28530_0]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h20408, hlam, p28530_0]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h26804, hlam, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h27373, hlam, p28530_0]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h27730, hc01, hc34, hlam, hphi, ht12, ht23, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h27730, hc02, hc34, hlam, hphi, ht23, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [hlam, p28530_0]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h27730, hlam, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h18815, h27730, hc01, hc34, hlam, hphi, ht12, ht23, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h27730, h28468, h28523, hc01, hc23, hlam, hphi, ht12, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h0, h27730, h28468, h28523, hc01, hc23, hlam, hphi, ht12, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h27730, h28466, h28468, h28523, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [hlam, p28530_0]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h0, h27373, h27730, h28468, h28523, hc01, hc23, hlam, hphi, ht12, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h27730, h28466, h28468, h28523, hc01, hc23, hlam, hphi, ht12, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h0, h27730, h28466, h28468, h28523, hc01, hc23, hlam, hphi, ht12, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h28466, hlam, p28530_0]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [h28467, hlam, p28530_1]
                          · have p28530_0 := h28530c.1
                            have p28530_1 := h28530c.2.1
                            have p28530_2 := h28530c.2.2.1
                            have p28530_3 := h28530c.2.2.2
                            linarith only [hlam, p28530_0]
                        · linarith only [h27730, h28467, h28529, hlam]
                      · linarith only [h0, h26804, h27730, h28466, h28467, h28523, h28528, hc01, hc14, hlam, hphi]
                    · linarith only [h27730, h28468, h28523, h28527, hc03, hc35, hlam, hphi]
                  · linarith only [h28468, h28523, h28526, hlam]
                · linarith only [h16915, h27730, h28466, h28467, h28523, h28525, hc01, hc13, hlam, hphi]
              · linarith only [h27730, h28466, h28523, h28524, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28562 | h28562
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28563 | h28563
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28564 | h28564
                  · linarith only [h0, h28521, h28523, h28562, h28564, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h28468, h28564, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h16915, h28467, h28563, hlam]
              · linarith only [h14396, h28466, h28562, hlam]
    · linarith only [h27730, h28466, h28467, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h28570 | h28570
    · rcases m.htr 1 2 3 (by decide) (by decide) with h28571 | h28571
      · rcases m.htr 1 2 4 (by decide) (by decide) with h28572 | h28572
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28573 | h28573
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28574 | h28574
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28575 | h28575
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28576 | h28576
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28577 | h28577
                  · linarith only [h14396, h27730, h28571, h28577, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h20408, h28574, h28577, hc01, hc13, hlam, hphi]
                · linarith only [h16915, h26804, h28570, h28576, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h20408, h27730, h28574, h28575, hc02, hc35, hlam, hphi, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28582 | h28582
              · linarith only [h0, h20408, h28466, h28574, h28582, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28584 | h28584
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28585 | h28585
                  · linarith only [h28571, h28574, h28585, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28587 | h28587
                    · linarith only [h0, h20408, h28466, h28571, h28587, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28589 | h28589
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28590 | h28590
                        · rcases h0bigk with h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c | h28591c
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [hlam, p28591_0]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h0, hlam, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h14396, hlam, p28591_0]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h16915, hlam, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h18815, hlam, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h14396, h20408, h28582, h28590, hc01, hc34, hlam, hphi, ht12, ht23, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [hlam, p28591_0]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h20408, hlam, p28591_0]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h26804, hlam, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h27373, hlam, p28591_0]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h14396, h28582, h28590, hc01, hc34, hlam, hphi, ht12, ht23, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h14396, h28582, h28590, hc02, hc34, hlam, hphi, ht23, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [hlam, p28591_0]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h27730, hlam, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h28466, hlam, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h26804, h28572, hc01, hc12, hlam, hphi, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h0, h26804, h28572, hc01, hc12, hlam, hphi, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h0, h20408, h26804, h28572, hc01, hc12, hlam, hphi, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [hlam, p28591_0]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h0, h20408, h26804, h28466, h28572, hc01, hc12, hlam, hphi, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h26804, h28570, h28572, hc01, hc12, hlam, hphi, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h0, h26804, h28570, h28572, hc01, hc12, hlam, hphi, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h0, h20408, h26804, h28570, h28572, hc01, hc12, hlam, hphi, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [h28570, hlam, p28591_1]
                          · have p28591_0 := h28591c.1
                            have p28591_1 := h28591c.2.1
                            have p28591_2 := h28591c.2.2.1
                            have p28591_3 := h28591c.2.2.2
                            linarith only [hlam, p28591_0]
                        · linarith only [h16915, h26804, h28570, h28572, h28574, h28590, hc01, hc12, hlam, hphi]
                      · linarith only [h26804, h28570, h28589, hlam]
                · linarith only [h26804, h28570, h28572, h28584, hlam]
          · linarith only [h0, h26804, h28572, h28573, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h20408, h28571, h28572, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h28622 | h28622
        · linarith only [h0, h26804, h28571, h28622, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28624 | h28624
          · linarith only [h0, h27373, h28571, h28624, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28626 | h28626
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28627 | h28627
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28628 | h28628
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28629 | h28629
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28630 | h28630
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28631 | h28631
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28632 | h28632
                        · rcases h0bigk with h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c | h28633c
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [hlam, p28633_0]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h0, hlam, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h14396, hlam, p28633_0]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h16915, hlam, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h18815, hlam, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h20408, h28466, h28626, h28632, hc01, hc13, hlam, hphi, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [hlam, p28633_0]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h20408, hlam, p28633_0]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h26804, hlam, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h27373, hlam, p28633_0]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h28466, h28626, h28632, hc01, hc13, hlam, hphi, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h28466, h28626, h28632, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [hlam, p28633_0]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h27730, hlam, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h28466, hlam, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h27730, h28626, hc01, hc13, hlam, hphi, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h0, h27730, h28626, hc01, hc13, hlam, hphi, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h14396, h27730, h28626, hc01, hc13, hlam, hphi, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [hlam, p28633_0]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h0, h20408, h27730, h28466, h28626, hc01, hc13, hlam, hphi, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h28466, h28626, h28632, hc01, hc13, hlam, hphi, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h0, h28466, h28626, h28632, hc01, hc13, hlam, hphi, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h0, h20408, h28466, h28626, h28632, hc01, hc13, hlam, hphi, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [h28570, hlam, p28633_1]
                          · have p28633_0 := h28633c.1
                            have p28633_1 := h28633c.2.1
                            have p28633_2 := h28633c.2.2.1
                            have p28633_3 := h28633c.2.2.2
                            linarith only [hlam, p28633_0]
                        · linarith only [h27730, h28570, h28632, hlam]
                      · linarith only [h0, h26804, h27730, h28570, h28626, h28631, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h28622, h28629, h28630, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h28571, h28629, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h16915, h28570, h28628, hlam]
              · linarith only [h0, h20408, h27730, h28626, h28627, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28665 | h28665
              · linarith only [h0, h20408, h28466, h28626, h28665, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28667 | h28667
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28668 | h28668
                  · linarith only [h14396, h28626, h28668, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h28571, h28668, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h16915, h28570, h28667, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h28672 | h28672
      · rcases m.htr 1 2 4 (by decide) (by decide) with h28673 | h28673
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28674 | h28674
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28675 | h28675
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28676 | h28676
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28677 | h28677
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28678 | h28678
                  · linarith only [h14396, h27730, h28672, h28678, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h20408, h28672, h28675, h28678, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28681 | h28681
                  · linarith only [h0, h20408, h27730, h28672, h28681, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h20408, h28675, h28677, h28681, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h20408, h27730, h28675, h28676, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28685 | h28685
              · linarith only [h0, h20408, h28466, h28675, h28685, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28687 | h28687
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28688 | h28688
                  · linarith only [h14396, h28675, h28688, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28690 | h28690
                    · linarith only [h28672, h28685, h28690, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28692 | h28692
                      · linarith only [h0, h20408, h27730, h28570, h28673, h28692, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h26804, h28687, h28692, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28695 | h28695
                  · linarith only [h0, h20408, h27730, h28672, h28685, h28695, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28697 | h28697
                    · linarith only [h0, h20408, h28466, h28672, h28697, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28699 | h28699
                      · linarith only [h14396, h28675, h28687, h28699, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28701 | h28701
                        · linarith only [h0, h20408, h28672, h28675, h28687, h28701, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h20408, h28672, h28675, h28701, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h20408, h28672, h28674, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h20408, h28672, h28673, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h28706 | h28706
        · linarith only [h0, h26804, h28672, h28706, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28708 | h28708
          · linarith only [h0, h27373, h28672, h28708, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h28710 | h28710
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28711 | h28711
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28712 | h28712
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28713 | h28713
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28714 | h28714
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28715 | h28715
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28716 | h28716
                        · linarith only [h0, h20408, h27730, h28570, h28710, h28716, hc01, hc13, hlam, hphi]
                        · linarith only [h0, h20408, h27730, h28712, h28716, hc01, hc14, hlam, hphi]
                      · linarith only [h28706, h28712, h28715, hlam]
                    · linarith only [h0, h20408, h27730, h28570, h28706, h28712, h28713, h28714, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h20408, h27730, h28570, h28672, h28710, h28712, h28713, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28722 | h28722
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h28723 | h28723
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h28724 | h28724
                      · linarith only [h16915, h28712, h28722, h28724, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h28706, h28724, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h20408, h28711, h28723, hc01, hc13, hlam, hphi]
                  · linarith only [h0, h20408, h28466, h28672, h28711, h28722, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h20408, h27730, h28710, h28711, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h28730 | h28730
              · linarith only [h0, h20408, h28466, h28710, h28730, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h28732 | h28732
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28733 | h28733
                  · linarith only [h14396, h28710, h28733, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h28672, h28733, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h28736 | h28736
                  · linarith only [h0, h28672, h28710, h28736, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h28672, h28736, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 16662000 in
set_option maxHeartbeats 16662000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h20408 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h26804 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h27373 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  rcases m.htr 0 3 4 (by decide) (by decide) with h27730 | h27730
  · exact r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x1_x1_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 h20408 h26804 h27373 h27730
  · exact r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x1_x1_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 h20408 h26804 h27373 h27730

set_option maxHeartbeats 16662000 in
set_option maxHeartbeats 16662000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h20408 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h26804 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  rcases m.htr 0 2 5 (by decide) (by decide) with h27373 | h27373
  · exact r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x1_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 h20408 h26804 h27373
  · exact r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x1_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 h20408 h26804 h27373

set_option maxHeartbeats 16662000 in
set_option maxHeartbeats 16662000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s18_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h20408 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  rcases m.htr 0 2 4 (by decide) (by decide) with h26804 | h26804
  · exact r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 h20408 h26804
  · exact r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 h20408 h26804

set_option maxHeartbeats 16662000 in
set_option maxHeartbeats 16662000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s18 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  rcases m.htr 0 2 3 (by decide) (by decide) with h20408 | h20408
  · exact r1l7_10_12_23_L_I_L_I_H_I_s18_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 h20408
  · exact r1l7_10_12_23_L_I_L_I_H_I_s18_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 hg18815 h20408

end R2N4
