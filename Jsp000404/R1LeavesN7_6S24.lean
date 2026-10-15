import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S23

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6488000 in
set_option maxHeartbeats 6488000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s13 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  have h11024 := hg11024
  have h11558 := hg11558
  rcases m.htr 0 2 4 (by decide) (by decide) with h11559 | h11559
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s14 m hb0 hb2 hb4 h0 h6793 h10058 h11024 h11558 h11559
  · rcases m.htr 0 2 5 (by decide) (by decide) with h14427 | h14427
    · rcases m.htr 0 3 4 (by decide) (by decide) with h14428 | h14428
      · linarith only [h11558, h11559, h14428, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h14430 | h14430
        · rcases m.htr 0 4 5 (by decide) (by decide) with h14431 | h14431
          · rcases m.htr 1 2 3 (by decide) (by decide) with h14432 | h14432
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14433 | h14433
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14434 | h14434
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14435 | h14435
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14436 | h14436
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14437 | h14437
                      · linarith only [h11558, h11559, h14428, h14433, h14437, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14439 | h14439
                        · linarith only [h11558, h11559, h14432, h14435, h14437, h14439, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h11558, h11559, h14430, h14432, h14435, h14437, h14439, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h10058, h14431, h14436, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14443 | h14443
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14444 | h14444
                      · linarith only [h14435, h14444, h6793, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14446 | h14446
                        · linarith only [h11558, h11559, h14433, h14446, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h11558, h11559, h14430, h14433, h14446, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h11558, h11559, h14430, h14431, h14433, h14443, hlam]
                · linarith only [h11559, h14433, h14434, hc02, hc25, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14451 | h14451
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14452 | h14452
                  · linarith only [h14428, h14430, h14432, h14433, h14452, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14454 | h14454
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14455 | h14455
                      · linarith only [h11558, h14452, h14455, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14457 | h14457
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14458 | h14458
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14459 | h14459
                            · rcases h0bigk with h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c | h14460c
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [hlam, p14460_0]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h0, hlam, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h6793, hlam, p14460_0]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h10058, hlam, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h11024, hlam, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h0, h14433, h14455, hc01, hc34, hlam, hphi, ht12, ht23, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [hlam, p14460_0]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h0, h11558, h14433, h14455, h14457, h14459, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h11559, hlam, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h0, h11024, h14433, h14455, hc01, hc34, hlam, hphi, ht12, ht23, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h0, h11558, h14433, h14455, hc01, hc34, hlam, hphi, ht12, ht23, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h11558, hlam, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [hlam, p14460_0]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h14428, hlam, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h0, h11024, h11558, h14433, h14455, hc01, hc34, hlam, hphi, ht12, ht23, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                rcases p14460_3 (m.d 0 1) (by simp) with h14476 | h14476
                                · linarith only [h10058, h14476, hlam]
                                · rcases p14460_3 (m.d 0 2) (by simp) with h14478 | h14478
                                  · linarith only [h11559, h14478, hlam]
                                  · linarith only [h0, h14478, hlam]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h11558, h14457, h14459, hc45, hlam, hphi, ht0b, ht5b, p14460_1, u0elo3]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h11558, h14457, h14459, hc45, hlam, hphi, ht0b, ht5b, p14460_1, u0elo3]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [hlam, p14460_0]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                rcases p14460_3 (m.d 0 1) (by simp) with h14484 | h14484
                                · linarith only [h10058, h14484, hlam]
                                · rcases p14460_3 (m.d 0 2) (by simp) with h14486 | h14486
                                  · linarith only [h11559, h14486, hlam]
                                  · linarith only [h14427, h14486, hlam]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h11024, h14433, h14451, h14455, hc01, hc34, hlam, hphi, ht12, ht23, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h14427, hlam, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h14430, hlam, p14460_0]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [h14431, hlam, p14460_1]
                              · have p14460_0 := h14460c.1
                                have p14460_1 := h14460c.2.1
                                have p14460_2 := h14460c.2.2.1
                                have p14460_3 := h14460c.2.2.2
                                linarith only [hlam, p14460_0]
                            · linarith only [h0, h11558, h14433, h14455, h14459, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h11558, h14431, h14433, h14457, h14458, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h0, h11558, h14430, h14433, h14455, h14457, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h10058, h11558, h14430, h14431, h14433, h14454, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h14427, h14451, hlam]
            · linarith only [h0, h11558, h14432, hlam]
          · linarith only [h11558, h11559, h14430, h14431, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h14501 | h14501
          · rcases m.htr 1 2 3 (by decide) (by decide) with h14502 | h14502
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14503 | h14503
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14504 | h14504
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14505 | h14505
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14506 | h14506
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14507 | h14507
                      · linarith only [h11558, h11559, h14428, h14503, h14507, h6793, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14509 | h14509
                        · linarith only [h11558, h11559, h14430, h14502, h14505, h14507, h14509, h6793, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14511 | h14511
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14512 | h14512
                            · rcases h0bigk with h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c | h14513c
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [hlam, p14513_0]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h0, hlam, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h6793, hlam, p14513_0]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h10058, hlam, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11024, hlam, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11559, h14502, h14505, h14507, hc01, hc12, hlam, hphi, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [hlam, p14513_0]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11559, h14502, h14505, h14507, h6793, hc01, hc12, hlam, hphi, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11559, hlam, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11559, h14502, h14505, h14507, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h14430, hc01, hc35, hlam, hphi, ht12, ht23, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11558, hlam, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [hlam, p14513_0]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h14428, hlam, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h14430, hlam, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11559, h14502, h14505, h14507, hc01, hc12, hlam, hphi, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11559, h14427, h14502, h14505, h14507, h14509, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11559, h14502, h14505, h14507, h6793, hc01, hc12, hlam, hphi, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [hlam, p14513_0]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11559, h14430, h14502, h14505, h14507, h6793, hc01, hc12, hlam, hphi, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11559, h14427, h14502, h14505, h14507, hc01, hc12, hlam, hphi, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h14427, hlam, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h11559, h14427, h14502, h14505, h14507, h6793, hc01, hc12, hlam, hphi, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [h14501, hlam, p14513_1]
                              · have p14513_0 := h14513c.1
                                have p14513_1 := h14513c.2.1
                                have p14513_2 := h14513c.2.2.1
                                have p14513_3 := h14513c.2.2.2
                                linarith only [hlam, p14513_0]
                            · linarith only [h11558, h11559, h14507, h14512, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h11559, h14427, h14501, h14511, hlam]
                    · linarith only [h10058, h11559, h14427, h14501, h14506, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14542 | h14542
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14543 | h14543
                      · linarith only [h14505, h14543, h6793, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14545 | h14545
                        · linarith only [h11558, h11559, h14503, h14545, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14547 | h14547
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14548 | h14548
                            · rcases h0bigk with h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c | h14549c
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [hlam, p14549_0]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h0, hlam, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h6793, hlam, p14549_0]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h10058, hlam, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11024, hlam, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11559, h14503, hc01, hc12, hlam, hphi, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [hlam, p14549_0]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11559, h14503, h6793, hc01, hc12, hlam, hphi, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11559, hlam, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11559, h14503, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h14430, hc01, hc35, hlam, hphi, ht12, ht23, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11558, hlam, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [hlam, p14549_0]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h14428, hlam, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h14430, hlam, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11559, h14503, hc01, hc12, hlam, hphi, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11559, h14427, h14503, h14545, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11559, h14503, h6793, hc01, hc12, hlam, hphi, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [hlam, p14549_0]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11559, h14430, h14503, h6793, hc01, hc12, hlam, hphi, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11559, h14427, h14503, hc01, hc12, hlam, hphi, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h14427, hlam, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h11559, h14427, h14503, h6793, hc01, hc12, hlam, hphi, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [h14501, hlam, p14549_1]
                              · have p14549_0 := h14549c.1
                                have p14549_1 := h14549c.2.1
                                have p14549_2 := h14549c.2.2.1
                                have p14549_3 := h14549c.2.2.2
                                linarith only [hlam, p14549_0]
                            · linarith only [h11558, h11559, h14503, h14505, h14548, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h11559, h14427, h14501, h14547, hlam]
                    · linarith only [h11559, h14427, h14501, h14503, h14542, hlam]
                · linarith only [h11559, h14427, h14504, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14579 | h14579
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14580 | h14580
                  · linarith only [h14428, h14502, h14503, h14580, h6793, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14582 | h14582
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14583 | h14583
                      · linarith only [h11558, h14580, h14583, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14585 | h14585
                        · linarith only [h11558, h14430, h14585, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14587 | h14587
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14588 | h14588
                            · rcases h0bigk with h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c | h14589c
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [hlam, p14589_0]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h0, hlam, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h6793, hlam, p14589_0]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h10058, hlam, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h11024, hlam, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h0, h14503, h14583, hc01, hc34, hlam, hphi, ht12, ht23, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [hlam, p14589_0]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h0, h14503, h14583, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h11559, hlam, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h0, h14430, h14503, h14583, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h14430, hc01, hc35, hlam, hphi, ht12, ht23, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h11558, hlam, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [hlam, p14589_0]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h14428, hlam, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h14430, hlam, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                rcases p14589_3 (m.d 0 1) (by simp) with h14605 | h14605
                                · linarith only [h10058, h14605, hlam]
                                · rcases p14589_3 (m.d 0 2) (by simp) with h14607 | h14607
                                  · linarith only [h11559, h14607, hlam]
                                  · linarith only [h0, h14607, hlam]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h14427, h14585, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14589_1, u0elo3]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                rcases p14589_3 (m.d 0 1) (by simp) with h14611 | h14611
                                · linarith only [h10058, h14611, hlam]
                                · rcases p14589_3 (m.d 0 2) (by simp) with h14613 | h14613
                                  · linarith only [h11559, h14613, hlam]
                                  · linarith only [h11558, h14613, hlam]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [hlam, p14589_0]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                rcases p14589_3 (m.d 0 1) (by simp) with h14617 | h14617
                                · linarith only [h10058, h14617, hlam]
                                · rcases p14589_3 (m.d 0 2) (by simp) with h14619 | h14619
                                  · linarith only [h11559, h14619, hlam]
                                  · linarith only [h14427, h14619, hlam]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h0, h14427, h14503, h14583, hc01, hc34, hlam, hphi, ht12, ht23, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h14427, hlam, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h0, h14427, h14503, h14583, hc03, hc34, hlam, hphi, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [h14501, hlam, p14589_1]
                              · have p14589_0 := h14589c.1
                                have p14589_1 := h14589c.2.1
                                have p14589_2 := h14589c.2.2.1
                                have p14589_3 := h14589c.2.2.2
                                linarith only [hlam, p14589_0]
                            · linarith only [h0, h14503, h14583, h14588, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h14501, h14502, h14503, h14587, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h10058, h14427, h14501, h14503, h14582, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h14427, h14579, hlam]
            · linarith only [h0, h11558, h14502, hlam]
          · linarith only [h11559, h14427, h14501, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h14633 | h14633
      · linarith only [h11558, h11559, h14633, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h14635 | h14635
        · linarith only [h11558, h14427, h14635, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h14637 | h14637
          · rcases m.htr 1 2 3 (by decide) (by decide) with h14638 | h14638
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14639 | h14639
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14640 | h14640
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14641 | h14641
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14642 | h14642
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14643 | h14643
                      · linarith only [h11558, h14633, h14643, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14645 | h14645
                        · linarith only [h11558, h11559, h14635, h14638, h14641, h14643, h14645, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14647 | h14647
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14648 | h14648
                            · rcases h0bigk with h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c | h14649c
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [hlam, p14649_0]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h0, hlam, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h6793, hlam, p14649_0]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h10058, hlam, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h11024, hlam, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h14427, h14638, h14641, h14643, h14647, hc01, hc12, hlam, hphi, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [hlam, p14649_0]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h14427, h14638, h14641, h14643, h14647, h6793, hc01, hc12, hlam, hphi, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h11559, hlam, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h14427, hlam, p14649_0]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h11558, h14427, h14638, h14641, h14643, h14647, hc01, hc12, hlam, hphi, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h11558, hlam, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [hlam, p14649_0]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h14633, hlam, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h14635, hlam, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h11559, h14638, h14641, h14643, hc01, hc12, hlam, hphi, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h11558, h11559, h14638, h14641, h14643, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h11559, h14638, h14641, h14643, h6793, hc01, hc12, hlam, hphi, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [hlam, p14649_0]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h11558, h11559, h14427, h14638, h14641, h14643, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h14427, h14638, h14641, h14643, h14647, hc01, hc12, hlam, hphi, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h11558, h14427, h14638, h14641, h14643, h14647, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h14427, h14638, h14641, h14643, h14647, h6793, hc01, hc12, hlam, hphi, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [h14637, hlam, p14649_1]
                              · have p14649_0 := h14649c.1
                                have p14649_1 := h14649c.2.1
                                have p14649_2 := h14649c.2.2.1
                                have p14649_3 := h14649c.2.2.2
                                linarith only [hlam, p14649_0]
                            · linarith only [h11559, h14637, h14643, h14648, hlam]
                          · linarith only [h11559, h14637, h14647, hlam]
                    · linarith only [h10058, h14637, h14642, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14678 | h14678
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14679 | h14679
                      · linarith only [h11558, h14641, h14679, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14681 | h14681
                        · linarith only [h11558, h11559, h14635, h14639, h14681, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14683 | h14683
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14684 | h14684
                            · rcases h0bigk with h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c | h14685c
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [hlam, p14685_0]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h0, hlam, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h6793, hlam, p14685_0]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h10058, hlam, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h11024, hlam, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h14427, h14639, h14683, hc01, hc12, hlam, hphi, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [hlam, p14685_0]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h14427, h14639, h14683, h6793, hc01, hc12, hlam, hphi, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h11559, hlam, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h14427, hlam, p14685_0]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h11558, h14427, h14639, h14683, hc01, hc12, hlam, hphi, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h11558, hlam, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [hlam, p14685_0]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h14633, hlam, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h14635, hlam, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h11559, h14639, hc01, hc12, hlam, hphi, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h11558, h11559, h14639, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h11559, h14639, h6793, hc01, hc12, hlam, hphi, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [hlam, p14685_0]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h11558, h11559, h14427, h14639, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h14427, h14639, h14683, hc01, hc12, hlam, hphi, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h11558, h14427, h14639, h14683, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h14427, h14639, h14683, h6793, hc01, hc12, hlam, hphi, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [h14637, hlam, p14685_1]
                              · have p14685_0 := h14685c.1
                                have p14685_1 := h14685c.2.1
                                have p14685_2 := h14685c.2.2.1
                                have p14685_3 := h14685c.2.2.2
                                linarith only [hlam, p14685_0]
                            · linarith only [h11559, h14637, h14639, h14641, h14684, hlam]
                          · linarith only [h11559, h14637, h14683, hlam]
                    · linarith only [h11559, h14637, h14639, h14678, hlam]
                · linarith only [h11558, h11559, h14639, h14640, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14715 | h14715
                · linarith only [h11558, h14427, h14639, h14715, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14717 | h14717
                  · linarith only [h14633, h14638, h14639, h14717, h6793, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14719 | h14719
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14720 | h14720
                      · linarith only [h11558, h14717, h14720, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14722 | h14722
                        · linarith only [h11558, h14635, h14722, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14724 | h14724
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h14725 | h14725
                            · rcases h0bigk with h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c | h14726c
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [hlam, p14726_0]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h0, hlam, p14726_1]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h6793, hlam, p14726_0]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h10058, hlam, p14726_1]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h11024, hlam, p14726_1]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h0, h14715, h14720, h14724, hc01, hc34, hlam, hphi, ht12, ht23, p14726_1]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [hlam, p14726_0]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h0, h14715, h14720, h14724, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p14726_1]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h11559, hlam, p14726_1]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h14427, hlam, p14726_0]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h14638, h14715, h14720, h14724, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p14726_1]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h11558, hlam, p14726_1]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [hlam, p14726_0]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h14633, hlam, p14726_1]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h14635, hlam, p14726_1]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                rcases p14726_3 (m.d 0 1) (by simp) with h14742 | h14742
                                · linarith only [h10058, h14742, hlam]
                                · rcases p14726_3 (m.d 0 2) (by simp) with h14744 | h14744
                                  · linarith only [h11559, h14744, hlam]
                                  · linarith only [h0, h14744, hlam]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h11558, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14726_1, u0elo3]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                rcases p14726_3 (m.d 0 1) (by simp) with h14748 | h14748
                                · linarith only [h10058, h14748, hlam]
                                · rcases p14726_3 (m.d 0 2) (by simp) with h14750 | h14750
                                  · linarith only [h11559, h14750, hlam]
                                  · linarith only [h11558, h14750, hlam]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [hlam, p14726_0]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h11558, h14427, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14726_1, u0elo3]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                rcases p14726_3 (m.d 0 1) (by simp) with h14755 | h14755
                                · linarith only [h11024, h14755, hlam]
                                · rcases p14726_3 (m.d 0 2) (by simp) with h14757 | h14757
                                  · linarith only [h14427, h14757, hlam]
                                  · linarith only [h0, h14757, hlam]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h11558, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14726_1, u0elo4]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                rcases p14726_3 (m.d 0 1) (by simp) with h14761 | h14761
                                · linarith only [h11024, h14761, hlam]
                                · rcases p14726_3 (m.d 0 2) (by simp) with h14763 | h14763
                                  · linarith only [h14427, h14763, hlam]
                                  · linarith only [h11558, h14763, hlam]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [h14637, hlam, p14726_1]
                              · have p14726_0 := h14726c.1
                                have p14726_1 := h14726c.2.1
                                have p14726_2 := h14726c.2.2.1
                                have p14726_3 := h14726c.2.2.2
                                linarith only [hlam, p14726_0]
                            · linarith only [h14637, h14715, h14720, h14724, h14725, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h14637, h14638, h14639, h14724, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h10058, h14637, h14719, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
            · linarith only [h0, h11558, h14638, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h14772 | h14772
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14773 | h14773
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14774 | h14774
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14775 | h14775
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14776 | h14776
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14777 | h14777
                      · linarith only [h11558, h14633, h14777, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14779 | h14779
                        · linarith only [h11558, h11559, h14637, h14772, h14775, h14776, h14779, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14781 | h14781
                          · linarith only [h11558, h11559, h14637, h14772, h14775, h14777, h14781, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h11558, h11559, h14781, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h11558, h11559, h14773, h14776, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14785 | h14785
                    · linarith only [h11558, h11559, h14637, h14775, h14785, hc23, hc34, hlam, hphi]
                    · linarith only [h11558, h11559, h14773, h14785, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h11558, h11559, h14773, h14774, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14789 | h14789
                · linarith only [h11558, h14427, h14773, h14789, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14791 | h14791
                  · linarith only [h14633, h14772, h14773, h14791, h6793, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h14793 | h14793
                    · linarith only [h11558, h11559, h14637, h14791, h14793, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14795 | h14795
                      · linarith only [h11558, h14633, h14795, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h14797 | h14797
                        · linarith only [h0, h11024, h11558, h14635, h14773, h14793, h14797, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h14799 | h14799
                          · linarith only [h0, h11558, h14773, h14793, h14795, h14799, hc23, hc34, hlam, hphi]
                          · linarith only [h11558, h11559, h14799, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h11558, h11559, h14772, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 9982000 in
set_option maxHeartbeats 9982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s12_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  have h11024 := hg11024
  exact r1l7_20_12_14_M_LI_L_I_L_I_s13 m hb0 hb2 hb4 h0 h6793 h10058 h11024 h11558

end R2N4
