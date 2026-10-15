import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S25
import Jsp000404.R1LeavesN7_1S30
import Jsp000404.R1LeavesN7_1S52
import Jsp000404.R1LeavesN7_1S55
import Jsp000404.R1LeavesN7_1S56

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h19727 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 4 (by decide) (by decide) with h20418 | h20418
  · rcases m.htr 0 2 5 (by decide) (by decide) with h20419 | h20419
    · rcases m.htr 0 3 4 (by decide) (by decide) with h20420 | h20420
      · rcases m.htr 0 3 5 (by decide) (by decide) with h20421 | h20421
        · rcases m.htr 0 4 5 (by decide) (by decide) with h20422 | h20422
          · linarith only [h18443, h18444, h20422, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20424 | h20424
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20425 | h20425
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20426 | h20426
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20427 | h20427
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20428 | h20428
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20429 | h20429
                      · linarith only [h18443, h18444, h19727, h20419, h20422, h20424, h20429, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20431 | h20431
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20432 | h20432
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20433 | h20433
                            · linarith only [h18443, h18444, h20425, h20429, h20433, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20435 | h20435
                              · linarith only [h18443, h18444, h20425, h20429, h20431, h20435, hlam]
                              · rcases h0bigk with h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c | h20437c
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [hlam, p20437_0]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h0, hlam, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h15532, hlam, p20437_0]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h18444, h19727, h20419, h20424, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h18444, hlam, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h19727, h20424, hc01, hc12, hlam, hphi, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [hlam, p20437_0]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h19727, hlam, p20437_0]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h18443, h19727, h20424, h20425, h20431, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h19727, h20424, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h18443, h19727, h20424, h20425, h20431, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h19727, h20419, h20424, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [hlam, p20437_0]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  rcases p20437_3 (m.d 0 1) (by simp) with h20451 | h20451
                                  · linarith only [h15532, h20451, hlam]
                                  · linarith only [h18443, h20451, hlam]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h18443, h18444, h19727, h20424, h20425, h20431, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h18443, hlam, p20437_0]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h20418, hlam, p20437_0]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h20420, hlam, p20437_0]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [hlam, p20437_0]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h20422, hlam, p20437_0]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h18443, h18444, h20425, h20429, h20431, hc34, hc45, hlam, hphi, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h20419, hlam, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h20421, hlam, p20437_0]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [h18443, h19727, h20419, h20424, h20425, h20431, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20437_1]
                                · have p20437_0 := h20437c.1
                                  have p20437_1 := h20437c.2.1
                                  have p20437_2 := h20437c.2.2.1
                                  have p20437_3 := h20437c.2.2.2
                                  linarith only [hlam, p20437_0]
                          · linarith only [h19727, h20421, h20432, hlam]
                        · linarith only [h19727, h20420, h20431, hlam]
                    · linarith only [h15532, h18443, h19727, h20419, h20421, h20425, h20428, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h15532, h20420, h20427, hlam]
                · linarith only [h19727, h20424, h20426, hc02, hc25, hlam, hphi]
              · linarith only [h18443, h18444, h19727, h20419, h20424, h20425, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20471 | h20471
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20472 | h20472
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20473 | h20473
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20474 | h20474
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20475 | h20475
                      · linarith only [h18443, h18444, h20424, h20472, h20475, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20477 | h20477
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20478 | h20478
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20479 | h20479
                            · linarith only [h18443, h18444, h20471, h20475, h20479, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20481 | h20481
                              · linarith only [h18443, h18444, h20471, h20475, h20477, h20481, hlam]
                              · rcases h0bigk with h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c | h20483c
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [hlam, p20483_0]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h0, hlam, p20483_1]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h15532, hlam, p20483_0]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h18444, h20424, h20472, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20483_1]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h18444, hlam, p20483_1]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h0, h20424, hc01, hc23, hlam, hphi, ht12, p20483_1]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [hlam, p20483_0]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h19727, hlam, p20483_0]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  rcases p20483_3 (m.d 0 1) (by simp) with h20492 | h20492
                                  · linarith only [h0, h20492, hlam]
                                  · linarith only [h18443, h20492, hlam]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h0, h18443, h18444, h20424, h20471, h20477, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20483_1]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  rcases p20483_3 (m.d 0 1) (by simp) with h20496 | h20496
                                  · linarith only [h15532, h20496, hlam]
                                  · rcases p20483_3 (m.d 0 2) (by simp) with h20498 | h20498
                                    · linarith only [h19727, h20498, hlam]
                                    · linarith only [h0, h20498, hlam]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  rcases p20483_3 (m.d 0 1) (by simp) with h20501 | h20501
                                  · linarith only [h15532, h20501, hlam]
                                  · rcases p20483_3 (m.d 0 2) (by simp) with h20503 | h20503
                                    · linarith only [h19727, h20503, hlam]
                                    · rcases p20483_3 (m.d 0 3) (by simp) with h20505 | h20505
                                      · rcases p20483_3 (m.d 0 4) (by simp) with h20506 | h20506
                                        · linarith only [h20420, h20506, hlam]
                                        · rcases p20483_3 (m.d 0 5) (by simp) with h20508 | h20508
                                          · linarith only [h20421, h20508, hlam]
                                          · rcases h2bigk with h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c | h20510c
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [hlam, p20510_0]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h0, hlam, p20510_1]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h19727, hlam, p20510_0]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h15532, h20424, h20477, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20483_1, p20510_1]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h15532, h20424, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p20483_1, p20510_1]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h20424, hc02, hc23, hlam, hphi, p20510_1]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [hlam, p20510_0]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h20424, hlam, p20510_0]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              rcases p20510_3 (m.d 0 2) (by simp) with h20519 | h20519
                                              · linarith only [h0, h20519, hlam]
                                              · linarith only [h20418, h20519, hlam]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              rcases p20510_3 (m.d 0 2) (by simp) with h20522 | h20522
                                              · linarith only [h0, h20522, hlam]
                                              · linarith only [h20419, h20522, hlam]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              rcases p20510_3 (m.d 0 2) (by simp) with h20525 | h20525
                                              · linarith only [h20525, hlam, p20510_0]
                                              · rcases p20510_3 (m.d 1 2) (by simp) with h20527 | h20527
                                                · linarith only [h20424, h20527, hlam]
                                                · linarith only [h0, h20527, hlam]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h0, h18443, h20471, h20477, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p20510_1]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [hlam, p20510_0]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h15532, h18443, h18444, h20419, h20424, h20471, hlam, p20483_1, p20510_2]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h15532, h20419, h20424, hlam, p20483_1, p20510_2]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h20418, hlam, p20510_0]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h20471, hlam, p20510_0]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h20477, hlam, p20510_1]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [hlam, p20510_0]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h20479, hlam, p20510_1]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h20419, hlam, p20510_0]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h20472, hlam, p20510_0]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h20478, hlam, p20510_1]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [h20419, h20477, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p20483_1, p20510_1]
                                            · have p20510_0 := h20510c.1
                                              have p20510_1 := h20510c.2.1
                                              have p20510_2 := h20510c.2.2.1
                                              have p20510_3 := h20510c.2.2.2
                                              linarith only [hlam, p20510_0]
                                      · linarith only [h19727, h20505, hlam]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [hlam, p20483_0]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  rcases p20483_3 (m.d 0 1) (by simp) with h20546 | h20546
                                  · linarith only [h15532, h20546, hlam]
                                  · linarith only [h18443, h20546, hlam]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  rcases p20483_3 (m.d 0 1) (by simp) with h20549 | h20549
                                  · linarith only [h15532, h20549, hlam]
                                  · rcases p20483_3 (m.d 0 2) (by simp) with h20551 | h20551
                                    · linarith only [h19727, h20551, hlam]
                                    · linarith only [h20419, h20551, hlam]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h18443, hlam, p20483_0]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h20418, hlam, p20483_0]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h20420, hlam, p20483_0]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [hlam, p20483_0]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h20422, hlam, p20483_0]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h18443, h18444, h20471, h20475, h20477, hc34, hc45, hlam, hphi, p20483_1]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h20419, hlam, p20483_1]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [h20421, hlam, p20483_0]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  rcases p20483_3 (m.d 0 1) (by simp) with h20562 | h20562
                                  · linarith only [h18444, h20562, hlam]
                                  · linarith only [h18443, h20562, hlam]
                                · have p20483_0 := h20483c.1
                                  have p20483_1 := h20483c.2.1
                                  have p20483_2 := h20483c.2.2.1
                                  have p20483_3 := h20483c.2.2.2
                                  linarith only [hlam, p20483_0]
                          · linarith only [h0, h18443, h20424, h20471, h20477, h20478, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h18443, h18444, h20424, h20471, h20472, h20477, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h15532, h18443, h20419, h20421, h20424, h20471, h20474, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h15532, h18443, h19727, h20420, h20424, h20473, hc02, hc23, hlam, hphi]
                · linarith only [h0, h18443, h20419, h20472, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h20418, h20471, hlam]
        · linarith only [h19727, h20419, h20421, hlam]
      · linarith only [h0, h18443, h19727, h20420, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h20574 | h20574
      · rcases m.htr 0 3 5 (by decide) (by decide) with h20575 | h20575
        · rcases m.htr 0 4 5 (by decide) (by decide) with h20576 | h20576
          · linarith only [h0, h18443, h20419, h20576, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20578 | h20578
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20579 | h20579
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20580 | h20580
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20581 | h20581
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20582 | h20582
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20583 | h20583
                      · linarith only [h0, h18443, h19727, h20576, h20578, h20583, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20585 | h20585
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20586 | h20586
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20587 | h20587
                            · linarith only [h0, h18443, h20419, h20579, h20580, h20583, h20587, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20589 | h20589
                              · linarith only [h0, h18443, h20419, h20574, h20580, h20583, h20589, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0bigk with h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c | h20591c
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h0, hlam, p20591_1]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h15532, hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h0, h20419, h20580, h20583, hc04, hc45, hlam, hphi, p20591_1]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h18444, hlam, p20591_1]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h20419, h20580, hc01, hc15, hlam, hphi, p20591_1]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h19727, hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h18443, h19727, h20578, h20579, h20585, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20591_1]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h20419, hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h19727, h20578, hc01, hc12, hlam, hphi, p20591_1]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h0, h18443, h19727, h20578, h20579, h20585, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20591_1]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  rcases p20591_3 (m.d 0 1) (by simp) with h20605 | h20605
                                  · linarith only [h15532, h20605, hlam]
                                  · linarith only [h18443, h20605, hlam]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h18443, h18444, h19727, h20578, h20579, h20585, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20591_1]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h18443, hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h20418, hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h20574, hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h20576, hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h18443, h18444, h20579, h20583, h20585, hc34, hc45, hlam, hphi, p20591_1]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h0, h18443, h20419, h20578, h20579, h20585, h20586, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p20591_1]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [h20575, hlam, p20591_0]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  rcases p20591_3 (m.d 0 1) (by simp) with h20617 | h20617
                                  · linarith only [h18444, h20617, hlam]
                                  · linarith only [h18443, h20617, hlam]
                                · have p20591_0 := h20591c.1
                                  have p20591_1 := h20591c.2.1
                                  have p20591_2 := h20591c.2.2.1
                                  have p20591_3 := h20591c.2.2.2
                                  linarith only [hlam, p20591_0]
                          · linarith only [h19727, h20575, h20586, hlam]
                        · linarith only [h0, h18443, h19727, h20574, h20579, h20585, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h15532, h20575, h20582, hlam]
                  · linarith only [h15532, h18443, h20574, h20579, h20581, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h18443, h19727, h20578, h20579, h20580, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h18443, h19727, h20578, h20579, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20627 | h20627
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20628 | h20628
                · linarith only [h0, h18443, h20419, h20578, h20627, h20628, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20630 | h20630
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20631 | h20631
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20632 | h20632
                      · linarith only [h0, h18443, h20578, h20632, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20634 | h20634
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20635 | h20635
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20636 | h20636
                            · linarith only [h0, h18443, h20627, h20628, h20632, h20635, h20636, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h18443, h20627, h20628, h20634, h20636, hc34, hc45, hlam, hphi]
                          · linarith only [h15532, h18443, h20575, h20578, h20627, h20634, h20635, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h18443, h20578, h20627, h20634, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h15532, h20575, h20631, hlam]
                  · linarith only [h15532, h20574, h20630, hlam]
              · linarith only [h0, h20418, h20627, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h20644 | h20644
          · linarith only [h18443, h18444, h20644, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20646 | h20646
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20647 | h20647
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20648 | h20648
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20649 | h20649
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20650 | h20650
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20651 | h20651
                      · linarith only [h0, h18443, h19727, h20644, h20651, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20653 | h20653
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20654 | h20654
                          · linarith only [h0, h19727, h20575, h20646, h20654, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h18443, h19727, h20647, h20650, h20653, h20654, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h18443, h19727, h20574, h20575, h20653, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20658 | h20658
                      · linarith only [h15532, h18443, h20650, h20658, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20660 | h20660
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20661 | h20661
                          · linarith only [h20646, h20650, h20661, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20663 | h20663
                            · linarith only [h0, h18443, h19727, h20419, h20646, h20647, h20648, h20650, h20658, h20663, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h20665 | h20665
                              · linarith only [h0, h18443, h19727, h20646, h20647, h20650, h20658, h20660, h20665, hlam]
                              · linarith only [h0, h18443, h19727, h20646, h20650, h20665, hc14, hc45, hlam, hphi]
                        · linarith only [h0, h18443, h19727, h20574, h20647, h20660, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h18443, h19727, h20574, h20646, h20649, hlam]
                · linarith only [h0, h18443, h19727, h20646, h20647, h20648, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h18443, h19727, h20646, h20647, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h20672 | h20672
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20673 | h20673
                · linarith only [h0, h18443, h20419, h20646, h20672, h20673, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20675 | h20675
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h20676 | h20676
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20677 | h20677
                      · linarith only [h0, h18443, h20646, h20677, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20679 | h20679
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20680 | h20680
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h20681 | h20681
                            · linarith only [h0, h18443, h19727, h20575, h20646, h20672, h20676, h20677, h20681, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h18443, h20672, h20673, h20679, h20681, hc34, hc45, hlam, hphi]
                          · linarith only [h20646, h20676, h20680, hlam]
                        · linarith only [h0, h18443, h19727, h20575, h20646, h20672, h20676, h20679, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h20686 | h20686
                      · linarith only [h0, h18443, h20644, h20646, h20676, h20686, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h20688 | h20688
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20689 | h20689
                          · linarith only [h0, h18443, h20646, h20672, h20676, h20688, h20689, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h18443, h20646, h20672, h20688, h20689, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h18443, h20646, h20672, h20688, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h18443, h20574, h20646, h20672, h20675, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h20418, h20672, hlam]
      · linarith only [h15532, h18443, h20574, hlam]
  · linarith only [h0, h18443, h20418, hlam]

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h18444 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 3 (by decide) (by decide) with h19727 | h19727
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h19727
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444 h19727

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 1 5 (by decide) (by decide) with h18444 | h18444
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443 h18444

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s19 m hb0 hb2 hb3 hb5 h0 h15532 h18443

set_option maxHeartbeats 27248000 in
set_option maxHeartbeats 27248000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 1 4 (by decide) (by decide) with h18443 | h18443
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h18443

set_option maxHeartbeats 33070000 in
set_option maxHeartbeats 33070000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s16 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h15532 | h15532
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17 m hb0 hb2 hb3 hb5 h0 h15532
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s18 m hb0 hb2 hb3 hb5 h0 h15532

set_option maxHeartbeats 64134000 in
set_option maxHeartbeats 64134000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5bigk := hb5.1
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s16 m hb0 hb2 hb3 hb5 h0

end R2N4
