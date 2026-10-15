import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_75S0

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_R_L_R_H_I_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h410 | h410
  · rcases m.htr 0 2 3 (by decide) (by decide) with h411 | h411
    · rcases m.htr 0 3 4 (by decide) (by decide) with h412 | h412
      · rcases m.htr 1 2 3 (by decide) (by decide) with h413 | h413
        · rcases m.htr 1 3 4 (by decide) (by decide) with h414 | h414
          · rcases m.htr 1 3 5 (by decide) (by decide) with h415 | h415
            · rcases m.htr 2 3 4 (by decide) (by decide) with h416 | h416
              · rcases m.htr 2 3 5 (by decide) (by decide) with h417 | h417
                · rcases m.htr 3 4 5 (by decide) (by decide) with h418 | h418
                  · linarith only [h0, h410, h413, h416, h418, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases h3bigk with h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h413, h416, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p420_1, u2ehi3]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h0, h410, h416, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p420_1, u2ehi3]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h0, h410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p420_1]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h0, h410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p420_1]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h410, hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h416, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p420_1, u2ehi3]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h0, h410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p420_1]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h0, h410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p420_1]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h411, hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h413, hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h411, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p420_1]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h0, h410, h413, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p420_1]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h412, hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h414, hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h416, hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h418, hlam, p420_1]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p420_1]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h415, hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h417, hlam, p420_0]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [h410, h413, h417, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p420_1]
                    · have p420_0 := h420c.1
                      have p420_1 := h420c.2.1
                      have p420_2 := h420c.2.2.1
                      have p420_3 := h420c.2.2.2
                      linarith only [hlam, p420_0]
                · linarith only [h0, h410, h415, h417, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h410, h412, h416, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h448 | h448
              · rcases m.htr 2 3 5 (by decide) (by decide) with h449 | h449
                · linarith only [h413, h415, h449, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h451 | h451
                  · linarith only [h0, h410, h413, h448, h451, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases h3bigk with h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h0, h410, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p453_1]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h0, h410, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p453_1, u2ehi2]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h0, h410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p453_1]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h0, h410, h413, h415, h448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p453_1, u2ehi3]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h410, hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h448, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p453_1, u2ehi3]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h0, h410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p453_1]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h415, hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h411, hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h413, hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h0, h410, h413, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p453_1]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h449, hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h412, hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h414, hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h448, hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [hlam, p453_0]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h451, hlam, p453_1]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h451, hc03, hc45, hlam, hphi, ht34, p453_1]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h413, h448, h451, hc45, hlam, hphi, ht23, ht34, p453_1, u2ehi3]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h448, h451, hc45, hlam, hphi, ht23, ht34, p453_1, u2ehi3]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [h451, hc34, hc45, hlam, hphi, p453_1]
                    · have p453_0 := h453c.1
                      have p453_1 := h453c.2.1
                      have p453_2 := h453c.2.2.1
                      have p453_3 := h453c.2.2.2
                      linarith only [hlam, p453_0]
              · linarith only [h0, h410, h412, h448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
          · linarith only [h0, h410, h412, h413, h414, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
        · linarith only [h0, h413, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h482 | h482
        · rcases m.htr 1 3 4 (by decide) (by decide) with h483 | h483
          · linarith only [h410, h412, h483, hc01, hlam, hphi, u0ehi2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h485 | h485
            · rcases m.htr 2 3 4 (by decide) (by decide) with h486 | h486
              · linarith only [h412, h486, hc23, hlam, hphi, ht01, ht12, u0ehi2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h488 | h488
                · rcases m.htr 3 4 5 (by decide) (by decide) with h489 | h489
                  · rcases h3bigk with h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c | h490c
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h482, h488, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p490_1, u2ehi4]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h412, h488, hc34, hlam, hphi, ht23, p490_1, u2ehi4]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h412, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h0, h410, h412, h482, h488, hc12, hc34, hc35, hlam, hphi, ht01, ht0b, ht23, ht5b, p490_1, u2ehi4]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h410, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h0, h410, h488, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p490_1, u2ehi4]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h483, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h0, h410, h489, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p490_1]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h411, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h482, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h486, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h0, h411, h489, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p490_1]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hc03, hc34, hlam, hphi, p490_1]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hc13, hc34, hlam, hphi, p490_1]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hc34, hlam, hphi, ht23, p490_1, u2ehi2]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      rcases p490_3 (m.d 0 3) (by simp) with h510 | h510
                      · linarith only [h412, h510, hlam]
                      · linarith only [h0, h410, h485, h510, hc12, hlam, hphi, ht01, u0ehi2]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h488, hc23, hlam, hphi, ht01, ht12, p490_1, u0ehi2]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h485, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h488, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [h489, hlam, p490_0]
                    · have p490_0 := h490c.1
                      have p490_1 := h490c.2.1
                      have p490_2 := h490c.2.2.1
                      have p490_3 := h490c.2.2.2
                      linarith only [hlam, p490_0]
                  · linarith only [h0, h410, h412, h482, h488, h489, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi2, u2ehi4]
                · linarith only [h0, h410, h485, h488, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h520 | h520
              · linarith only [h412, h520, hc23, hlam, hphi, ht01, ht12, u0ehi2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h522 | h522
                · linarith only [h482, h485, h522, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h524 | h524
                  · rcases h3bigk with h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c | h525c
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h482, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p525_1, u2ehi2]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h412, hc34, hlam, hphi, ht23, p525_1, u2ehi2]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h412, hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h412, h482, h485, hc34, hlam, hphi, ht23, p525_1, u2ehi2]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h410, hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h0, h410, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p525_1, u2ehi2]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h483, hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h485, hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h411, hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h482, hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h520, hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h522, hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [hc03, hc34, hlam, hphi, p525_1]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [hc13, hc34, hlam, hphi, p525_1]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [hc34, hlam, hphi, ht23, p525_1, u2ehi2]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h482, h485, hc34, hlam, hphi, ht23, p525_1, u2ehi2]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p525_1, u0ehi2]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h482, hc35, hlam, hphi, ht23, p525_1, u2ehi2]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [hc35, hlam, hphi, ht23, p525_1, u2ehi2]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [h524, hlam, p525_0]
                    · have p525_0 := h525c.1
                      have p525_1 := h525c.2.1
                      have p525_2 := h525c.2.2.1
                      have p525_3 := h525c.2.2.2
                      linarith only [hlam, p525_0]
                  · linarith only [h0, h410, h412, h482, h524, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi2, u2ehi2]
        · linarith only [h0, h482, hc23, hlam, hphi, ht01, ht12, u0ehi0]
    · linarith only [h0, h410, h411, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h554 | h554
    · rcases m.htr 0 3 4 (by decide) (by decide) with h555 | h555
      · rcases m.htr 1 2 3 (by decide) (by decide) with h556 | h556
        · rcases m.htr 1 3 4 (by decide) (by decide) with h557 | h557
          · rcases m.htr 1 3 5 (by decide) (by decide) with h558 | h558
            · rcases m.htr 2 3 4 (by decide) (by decide) with h559 | h559
              · rcases m.htr 2 3 5 (by decide) (by decide) with h560 | h560
                · rcases m.htr 3 4 5 (by decide) (by decide) with h561 | h561
                  · rcases h3bigk with h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h410, hlam, p562_1]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h559, h561, hc03, hc45, hlam, hphi, ht0b, ht5b, p562_1]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h554, h561, hc02, hc45, hlam, hphi, ht0b, ht5b, p562_1]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      rcases p562_3 (m.d 0 3) (by simp) with h567 | h567
                      · rcases p562_3 (m.d 1 3) (by simp) with h568 | h568
                        · rcases p562_3 (m.d 2 3) (by simp) with h569 | h569
                          · linarith only [h554, h569, hlam]
                          · linarith only [h560, h569, hlam]
                        · linarith only [h558, h568, hlam]
                      · linarith only [h567, hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h556, hc12, hlam, hphi, ht01, p562_1, u0ehi2]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h556, h559, h561, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p562_1]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h556, h561, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p562_1]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      rcases p562_3 (m.d 0 3) (by simp) with h578 | h578
                      · linarith only [h410, h578, hlam]
                      · linarith only [h554, h556, h559, h561, h578, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p562_1]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h554, hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h556, hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h554, h561, hc03, hc45, hlam, hphi, ht0b, ht5b, p562_1]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h0, h554, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p562_1]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h555, hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h557, hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h559, hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h410, h555, h556, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p562_1]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p562_1]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h558, hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h560, hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [h561, hlam, p562_0]
                    · have p562_0 := h562c.1
                      have p562_1 := h562c.2.1
                      have p562_2 := h562c.2.2.1
                      have p562_3 := h562c.2.2.2
                      linarith only [hlam, p562_0]
                  · rcases h3bigk with h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h410, hlam, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h560, h561, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      rcases p596_3 (m.d 0 3) (by simp) with h600 | h600
                      · rcases p596_3 (m.d 1 3) (by simp) with h601 | h601
                        · rcases p596_3 (m.d 2 3) (by simp) with h602 | h602
                          · linarith only [h554, h602, hlam]
                          · linarith only [h559, h602, hlam]
                        · linarith only [h557, h601, hlam]
                      · linarith only [h600, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      rcases p596_3 (m.d 0 3) (by simp) with h607 | h607
                      · rcases p596_3 (m.d 1 3) (by simp) with h608 | h608
                        · rcases p596_3 (m.d 2 3) (by simp) with h609 | h609
                          · linarith only [h554, h609, hlam]
                          · linarith only [h560, h609, hlam]
                        · linarith only [h558, h608, hlam]
                      · linarith only [h607, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h556, hc12, hlam, hphi, ht01, p596_1, u0ehi2]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h556, h560, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p596_1, u2ehi4]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      rcases p596_3 (m.d 0 3) (by simp) with h617 | h617
                      · linarith only [h410, h617, hlam]
                      · linarith only [h555, h617, hlam]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      rcases p596_3 (m.d 0 3) (by simp) with h620 | h620
                      · linarith only [h410, h620, hlam]
                      · linarith only [h410, h556, h620, hc01, hc12, hlam, hphi, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h554, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h556, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h554, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h0, h554, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h555, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h557, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h559, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h561, hlam, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h558, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h560, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h560, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hlam, p596_0]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h638 | h638
                  · linarith only [h556, h558, h559, h560, h638, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases h3bigk with h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h410, hlam, p640_1]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h559, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1, u2ehi3]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      rcases p640_3 (m.d 0 3) (by simp) with h644 | h644
                      · rcases p640_3 (m.d 1 3) (by simp) with h645 | h645
                        · rcases p640_3 (m.d 2 3) (by simp) with h646 | h646
                          · linarith only [h554, h646, hlam]
                          · linarith only [h559, h646, hlam]
                        · linarith only [h557, h645, hlam]
                      · linarith only [h644, hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h410, h556, h559, h560, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p640_1, u2ehi3]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h556, hc12, hlam, hphi, ht01, p640_1, u0ehi2]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h556, h559, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p640_1, u2ehi3]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      rcases p640_3 (m.d 0 3) (by simp) with h655 | h655
                      · linarith only [h410, h655, hlam]
                      · linarith only [h555, h655, hlam]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h556, h559, h560, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p640_1, u2ehi3]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h554, hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h556, hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h560, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p640_1]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h560, hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h555, hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h557, hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h559, hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h638, hlam, p640_1]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h410, h556, h558, hc12, hlam, hphi, ht01, p640_1, u0ehi0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h558, hlam, p640_0]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h556, h558, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p640_1]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [h556, h558, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p640_1]
                    · have p640_0 := h640c.1
                      have p640_1 := h640c.2.1
                      have p640_2 := h640c.2.2.1
                      have p640_3 := h640c.2.2.2
                      linarith only [hlam, p640_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h674 | h674
                · rcases m.htr 3 4 5 (by decide) (by decide) with h675 | h675
                  · rcases h3bigk with h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h410, hlam, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h674, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p676_1, u2ehi4]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h410, h556, h559, h674, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p676_1, u2ehi4]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      rcases p676_3 (m.d 0 3) (by simp) with h681 | h681
                      · rcases p676_3 (m.d 1 3) (by simp) with h682 | h682
                        · rcases p676_3 (m.d 2 3) (by simp) with h683 | h683
                          · linarith only [h554, h683, hlam]
                          · linarith only [h674, h683, hlam]
                        · linarith only [h558, h682, hlam]
                      · linarith only [h681, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h556, hc12, hlam, hphi, ht01, p676_1, u0ehi2]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h556, h674, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p676_1, u2ehi4]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h556, h559, h674, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p676_1, u2ehi4]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      rcases p676_3 (m.d 0 3) (by simp) with h692 | h692
                      · linarith only [h410, h692, hlam]
                      · linarith only [h555, h559, h674, h692, hlam]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h554, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h556, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h559, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h555, h559, hc03, hc35, hlam, hphi, ht0b, ht5b, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h555, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h557, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h555, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h410, h555, h556, h675, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p676_1]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h558, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h674, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [h675, hlam, p676_0]
                    · have p676_0 := h676c.1
                      have p676_1 := h676c.2.1
                      have p676_2 := h676c.2.2.1
                      have p676_3 := h676c.2.2.2
                      linarith only [hlam, p676_0]
                  · linarith only [h559, h674, h675, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h711 | h711
                  · rcases h3bigk with h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h410, hlam, p712_1]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h410, h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p712_1, u2ehi2]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h410, h556, h711, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p712_1]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h410, h556, h674, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p712_1, u2ehi2]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h556, hc12, hlam, hphi, ht01, p712_1, u0ehi2]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h556, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p712_1, u2ehi2]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h556, h674, h711, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p712_1, u2ehi2]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h556, h674, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p712_1, u2ehi2]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h554, hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h556, hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h559, hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h674, hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h555, hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h557, hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h554, h555, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p712_1, u2ehi2]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h0, h554, h555, h674, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p712_1, u2ehi2]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [hc03, hc35, hlam, hphi, p712_1]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h558, hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h556, h558, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p712_1, u2ehi2]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [h711, hlam, p712_0]
                    · have p712_0 := h712c.1
                      have p712_1 := h712c.2.1
                      have p712_2 := h712c.2.2.1
                      have p712_3 := h712c.2.2.2
                      linarith only [hlam, p712_0]
                  · linarith only [h559, h711, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h410, h558, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
          · linarith only [h410, h555, h557, hlam]
        · linarith only [h0, h556, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h742 | h742
        · rcases m.htr 1 3 4 (by decide) (by decide) with h743 | h743
          · linarith only [h555, h742, h743, hc12, hlam, hphi, ht01, u0ehi2]
          · linarith only [h410, h743, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
        · linarith only [h0, h554, h742, hc03, hlam, hphi, u0ehi0]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h747 | h747
      · rcases m.htr 1 2 3 (by decide) (by decide) with h748 | h748
        · linarith only [h554, h748, hc12, hlam, hphi, ht01, u0ehi1]
        · linarith only [h0, h748, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h751 | h751
        · linarith only [h0, h554, h751, hc12, hlam, hphi, ht01, u0ehi0]
        · linarith only [h0, h751, hc23, hlam, hphi, ht01, ht12, u0ehi0]

theorem r1l7_10_12_23_L_R_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_23_L_R_L_R_H_I_x0 m hb0 hb2 hb3 h0
  · exact r1l7_10_12_23_L_R_L_R_H_I_x1 m hb0 hb2 hb3 h0

end R2N4
