import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_49S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 1 2 4 (by decide) (by decide) with h627 | h627
  · rcases m.htr 1 2 5 (by decide) (by decide) with h628 | h628
    · rcases m.htr 1 3 4 (by decide) (by decide) with h629 | h629
      · rcases m.htr 1 3 5 (by decide) (by decide) with h630 | h630
        · rcases m.htr 1 4 5 (by decide) (by decide) with h631 | h631
          · rcases m.htr 2 3 4 (by decide) (by decide) with h632 | h632
            · rcases m.htr 2 3 5 (by decide) (by decide) with h633 | h633
              · rcases m.htr 2 4 5 (by decide) (by decide) with h634 | h634
                · rcases m.htr 3 4 5 (by decide) (by decide) with h635 | h635
                  · rcases h1bigk with h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c | h636c
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h627, h632, h635, hc01, hc45, hlam, hphi, ht0b, ht5b, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h627, h632, h635, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      rcases p636_3 (m.d 0 1) (by simp) with h640 | h640
                      · rcases p636_3 (m.d 1 2) (by simp) with h641 | h641
                        · linarith only [h0, h641, hlam]
                        · linarith only [h627, h641, hlam]
                      · linarith only [h640, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      rcases p636_3 (m.d 0 1) (by simp) with h645 | h645
                      · rcases p636_3 (m.d 1 2) (by simp) with h646 | h646
                        · linarith only [h0, h646, hlam]
                        · linarith only [h628, h646, hlam]
                      · linarith only [h645, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h0, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h7, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h631, hc12, hlam, hphi, p636_1, u1ehi4]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h7, hc23, hlam, hphi, ht12, p636_1, u1ehi4]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h1, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p636_1, u1ehi1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p636_1, u1ehi3]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p636_1, u1ehi4]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h2, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h627, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h629, hlam, p636_1]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hc14, hlam, hphi, p636_1, u1ehi4]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h3, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h628, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h630, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [h631, hlam, p636_0]
                    · have p636_0 := h636c.1
                      have p636_1 := h636c.2.1
                      have p636_2 := h636c.2.2.1
                      have p636_3 := h636c.2.2.2
                      linarith only [hlam, p636_0]
                  · linarith only [h627, h634, h635, h7, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h671 | h671
                  · linarith only [h1, h629, h634, h671, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h1bigk with h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c | h673c
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h627, h631, h632, h634, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p673_1]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h627, h631, h632, h634, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p673_1]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h631, h632, h634, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p673_1]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      rcases p673_3 (m.d 0 1) (by simp) with h678 | h678
                      · rcases p673_3 (m.d 1 2) (by simp) with h679 | h679
                        · linarith only [h0, h679, hlam]
                        · linarith only [h628, h679, hlam]
                      · linarith only [h678, hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h0, hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h7, hlam, p673_1]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h631, h632, h634, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p673_1]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h7, hc23, hlam, hphi, ht12, p673_1, u1ehi4]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h1, hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p673_1, u1ehi1]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h1, h631, h632, h634, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p673_1]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h1, h627, h631, h632, h634, h7, hc01, hc23, hc34, hlam, hphi, ht0b, ht12, ht45, ht5b, p673_1, u1ehi4]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h2, hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h627, hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h629, hlam, p673_1]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h627, h7, hc23, hlam, hphi, ht12, p673_1, u1ehi4]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h3, hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h628, hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h630, hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [h631, hlam, p673_0]
                    · have p673_0 := h673c.1
                      have p673_1 := h673c.2.1
                      have p673_2 := h673c.2.2.1
                      have p673_3 := h673c.2.2.2
                      linarith only [hlam, p673_0]
              · linarith only [h633, h7, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h627, h631, h632, h7, hc34, hlam, hphi, ht12, ht23, u1ehi4]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h705 | h705
            · rcases m.htr 2 3 5 (by decide) (by decide) with h706 | h706
              · rcases m.htr 2 4 5 (by decide) (by decide) with h707 | h707
                · linarith only [h631, h707, hc24, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h709 | h709
                  · linarith only [h628, h631, h7, h705, h707, h709, hc23, hlam, hphi, ht12, u1ehi3]
                  · rcases h1bigk with h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      rcases p711_3 (m.d 0 1) (by simp) with h713 | h713
                      · rcases p711_3 (m.d 1 2) (by simp) with h714 | h714
                        · linarith only [h714, hlam, p711_0]
                        · rcases p711_3 (m.d 1 3) (by simp) with h716 | h716
                          · linarith only [h1, h716, hlam]
                          · linarith only [h7, h716, hlam]
                      · linarith only [h713, hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      rcases p711_3 (m.d 0 1) (by simp) with h720 | h720
                      · rcases p711_3 (m.d 1 2) (by simp) with h721 | h721
                        · linarith only [h0, h721, hlam]
                        · rcases p711_3 (m.d 1 3) (by simp) with h723 | h723
                          · linarith only [h723, hlam, p711_0]
                          · rcases p711_3 (m.d 1 4) (by simp) with h725 | h725
                            · linarith only [h2, h725, hlam]
                            · rcases p711_3 (m.d 1 5) (by simp) with h727 | h727
                              · linarith only [h3, h727, hlam]
                              · rcases h4bigk with h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  rcases p729_3 (m.d 0 4) (by simp) with h731 | h731
                                  · rcases p729_3 (m.d 1 4) (by simp) with h732 | h732
                                    · linarith only [h2, h732, hlam]
                                    · rcases p729_3 (m.d 2 4) (by simp) with h734 | h734
                                      · linarith only [h4, h734, hlam]
                                      · rcases p729_3 (m.d 3 4) (by simp) with h736 | h736
                                        · linarith only [h5, h736, hlam]
                                        · rcases p729_3 (m.d 4 5) (by simp) with h738 | h738
                                          · linarith only [h6, h738, hlam]
                                          · linarith only [h631, h738, hlam]
                                  · linarith only [h2, h731, hlam]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  rcases p729_3 (m.d 0 4) (by simp) with h742 | h742
                                  · rcases p729_3 (m.d 1 4) (by simp) with h743 | h743
                                    · linarith only [h2, h743, hlam]
                                    · linarith only [h627, h743, hlam]
                                  · linarith only [h4, h742, hlam]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  rcases p729_3 (m.d 0 4) (by simp) with h747 | h747
                                  · rcases p729_3 (m.d 1 4) (by simp) with h748 | h748
                                    · linarith only [h2, h748, hlam]
                                    · linarith only [h629, h748, hlam]
                                  · linarith only [h5, h747, hlam]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h631, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p729_1, u1ehi3]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h2, hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h631, h705, hc34, hc45, hlam, hphi, p729_1]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h0, h4, h6, h631, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p729_1]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h631, hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h4, hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h627, hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h627, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p711_1, p729_1]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h707, hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h5, hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h629, hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h705, hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h709, hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h6, hlam, p729_0]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p729_1, u1ehi3]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  rcases p729_3 (m.d 0 4) (by simp) with h770 | h770
                                  · rcases p729_3 (m.d 1 4) (by simp) with h771 | h771
                                    · linarith only [h631, h771, hlam]
                                    · linarith only [h627, h771, hlam]
                                  · linarith only [h4, h770, hlam]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  rcases p729_3 (m.d 0 4) (by simp) with h775 | h775
                                  · rcases p729_3 (m.d 1 4) (by simp) with h776 | h776
                                    · linarith only [h631, h776, hlam]
                                    · linarith only [h629, h776, hlam]
                                  · linarith only [h5, h775, hlam]
                                · have p729_0 := h729c.1
                                  have p729_1 := h729c.2.1
                                  have p729_2 := h729c.2.2.1
                                  have p729_3 := h729c.2.2.2
                                  linarith only [hlam, p729_0]
                      · linarith only [h720, hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      rcases p711_3 (m.d 0 1) (by simp) with h782 | h782
                      · rcases p711_3 (m.d 1 2) (by simp) with h783 | h783
                        · linarith only [h0, h783, hlam]
                        · linarith only [h627, h783, hlam]
                      · linarith only [h782, hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      rcases p711_3 (m.d 0 1) (by simp) with h787 | h787
                      · rcases p711_3 (m.d 1 2) (by simp) with h788 | h788
                        · linarith only [h0, h788, hlam]
                        · linarith only [h628, h788, hlam]
                      · linarith only [h787, hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h0, hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h7, hlam, p711_1]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [hc12, hlam, hphi, p711_1, u1ehi3]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h7, hc23, hlam, hphi, ht12, p711_1, u1ehi4]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h1, hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h1, h628, hc01, hc25, hlam, hphi, ht0b, ht5b, p711_1]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p711_1, u1ehi3]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p711_1, u1ehi4]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h2, hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h627, hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h629, hlam, p711_1]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h631, hlam, p711_1]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h3, hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h628, hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [h630, hlam, p711_0]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [hc15, hlam, hphi, p711_1, u1ehi3]
                    · have p711_0 := h711c.1
                      have p711_1 := h711c.2.1
                      have p711_2 := h711c.2.2.1
                      have p711_3 := h711c.2.2.2
                      linarith only [hlam, p711_0]
              · linarith only [h628, h631, h7, h706, hc35, hlam, hphi, ht12, ht23, u1ehi3]
            · linarith only [h1, h5, h628, h631, h7, h705, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
        · linarith only [h628, h630, h7, hlam]
      · linarith only [h627, h629, h7, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h816 | h816
      · rcases m.htr 1 3 5 (by decide) (by decide) with h817 | h817
        · rcases m.htr 1 4 5 (by decide) (by decide) with h818 | h818
          · linarith only [h627, h628, h818, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h820 | h820
            · rcases m.htr 2 3 5 (by decide) (by decide) with h821 | h821
              · rcases m.htr 2 4 5 (by decide) (by decide) with h822 | h822
                · linarith only [h627, h628, h818, h821, h822, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h824 | h824
                  · linarith only [h627, h628, h820, h822, h824, hlam]
                  · rcases h1bigk with h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      rcases p826_3 (m.d 0 1) (by simp) with h828 | h828
                      · rcases p826_3 (m.d 1 2) (by simp) with h829 | h829
                        · linarith only [h829, hlam, p826_0]
                        · rcases p826_3 (m.d 1 3) (by simp) with h831 | h831
                          · linarith only [h1, h831, hlam]
                          · linarith only [h7, h831, hlam]
                      · linarith only [h828, hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      rcases p826_3 (m.d 0 1) (by simp) with h835 | h835
                      · rcases p826_3 (m.d 1 2) (by simp) with h836 | h836
                        · linarith only [h0, h836, hlam]
                        · rcases p826_3 (m.d 1 3) (by simp) with h838 | h838
                          · linarith only [h838, hlam, p826_0]
                          · rcases p826_3 (m.d 1 4) (by simp) with h840 | h840
                            · linarith only [h2, h840, hlam]
                            · rcases p826_3 (m.d 1 5) (by simp) with h842 | h842
                              · linarith only [h3, h842, hlam]
                              · rcases h4bigk with h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c | h844c
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  rcases p844_3 (m.d 0 4) (by simp) with h846 | h846
                                  · rcases p844_3 (m.d 1 4) (by simp) with h847 | h847
                                    · linarith only [h2, h847, hlam]
                                    · rcases p844_3 (m.d 2 4) (by simp) with h849 | h849
                                      · linarith only [h4, h849, hlam]
                                      · rcases p844_3 (m.d 3 4) (by simp) with h851 | h851
                                        · linarith only [h5, h851, hlam]
                                        · rcases p844_3 (m.d 4 5) (by simp) with h853 | h853
                                          · linarith only [h6, h853, hlam]
                                          · linarith only [h818, h853, hlam]
                                  · linarith only [h2, h846, hlam]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h6, h627, h628, h822, hlam, p844_2]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h6, h627, h628, h820, h822, hlam, p844_2]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h4, h627, h628, h822, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h2, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h627, h628, h820, h822, hc34, hc45, hlam, hphi, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h4, h6, h627, h628, h822, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h818, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h4, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h627, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h4, h6, h627, h628, h822, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p844_1]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h822, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h5, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h816, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h820, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h824, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h6, hlam, p844_0]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p844_1, u1ehi3]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  rcases p844_3 (m.d 0 4) (by simp) with h877 | h877
                                  · rcases p844_3 (m.d 1 4) (by simp) with h878 | h878
                                    · linarith only [h818, h878, hlam]
                                    · linarith only [h627, h878, hlam]
                                  · linarith only [h4, h877, hlam]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  rcases p844_3 (m.d 0 4) (by simp) with h882 | h882
                                  · rcases p844_3 (m.d 1 4) (by simp) with h883 | h883
                                    · linarith only [h818, h883, hlam]
                                    · linarith only [h816, h883, hlam]
                                  · linarith only [h5, h882, hlam]
                                · have p844_0 := h844c.1
                                  have p844_1 := h844c.2.1
                                  have p844_2 := h844c.2.2.1
                                  have p844_3 := h844c.2.2.2
                                  linarith only [hlam, p844_0]
                      · linarith only [h835, hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      rcases p826_3 (m.d 0 1) (by simp) with h889 | h889
                      · rcases p826_3 (m.d 1 2) (by simp) with h890 | h890
                        · linarith only [h0, h890, hlam]
                        · linarith only [h627, h890, hlam]
                      · linarith only [h889, hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      rcases p826_3 (m.d 0 1) (by simp) with h894 | h894
                      · rcases p826_3 (m.d 1 2) (by simp) with h895 | h895
                        · linarith only [h0, h895, hlam]
                        · rcases p826_3 (m.d 1 3) (by simp) with h897 | h897
                          · linarith only [h1, h897, hlam]
                          · linarith only [h817, h897, hlam]
                      · linarith only [h894, hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h0, hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h7, hlam, p826_1]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h0, h4, h6, h628, h822, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p826_1, u1ehi3]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h628, hlam, p826_1]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h1, hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [hc13, hlam, hphi, p826_1, u1ehi1]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p826_1, u1ehi3]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p826_1, u1ehi4]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h2, hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h627, hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h816, hlam, p826_1]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h818, hlam, p826_1]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h3, hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h627, hc15, hlam, hphi, p826_1, u1ehi3]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h817, hlam, p826_0]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [h0, h4, h6, h628, h822, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p826_1, u1ehi3]
                    · have p826_0 := h826c.1
                      have p826_1 := h826c.2.1
                      have p826_2 := h826c.2.2.1
                      have p826_3 := h826c.2.2.2
                      linarith only [hlam, p826_0]
              · linarith only [h7, h817, h821, hlam]
            · linarith only [h1, h5, h627, h7, h820, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h923 | h923
          · linarith only [h627, h628, h923, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h925 | h925
            · rcases m.htr 2 3 5 (by decide) (by decide) with h926 | h926
              · linarith only [h817, h926, hc23, hlam, hphi, ht12, u1ehi2]
              · linarith only [h627, h7, h926, hc35, hlam, hphi, ht12, ht23, u1ehi3]
            · linarith only [h627, h7, h925, hc34, hlam, hphi, ht12, ht23, u1ehi3]
      · linarith only [h627, h7, h816, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h931 | h931
    · rcases m.htr 1 3 4 (by decide) (by decide) with h932 | h932
      · rcases m.htr 1 3 5 (by decide) (by decide) with h933 | h933
        · rcases m.htr 1 4 5 (by decide) (by decide) with h934 | h934
          · rcases m.htr 2 3 4 (by decide) (by decide) with h935 | h935
            · rcases m.htr 2 3 5 (by decide) (by decide) with h936 | h936
              · rcases m.htr 2 4 5 (by decide) (by decide) with h937 | h937
                · rcases m.htr 3 4 5 (by decide) (by decide) with h938 | h938
                  · rcases h1bigk with h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      rcases p939_3 (m.d 0 1) (by simp) with h941 | h941
                      · rcases p939_3 (m.d 1 2) (by simp) with h942 | h942
                        · linarith only [h942, hlam, p939_0]
                        · rcases p939_3 (m.d 1 3) (by simp) with h944 | h944
                          · linarith only [h1, h944, hlam]
                          · linarith only [h7, h944, hlam]
                      · linarith only [h941, hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h932, h938, hc01, hc45, hlam, hphi, ht0b, ht5b, p939_1]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      rcases p939_3 (m.d 0 1) (by simp) with h949 | h949
                      · rcases p939_3 (m.d 1 2) (by simp) with h950 | h950
                        · linarith only [h0, h950, hlam]
                        · rcases p939_3 (m.d 1 3) (by simp) with h952 | h952
                          · linarith only [h1, h952, hlam]
                          · linarith only [h932, h952, hlam]
                      · linarith only [h949, hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      rcases p939_3 (m.d 0 1) (by simp) with h956 | h956
                      · rcases p939_3 (m.d 1 2) (by simp) with h957 | h957
                        · linarith only [h0, h957, hlam]
                        · linarith only [h931, h957, hlam]
                      · linarith only [h956, hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h0, hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h7, hlam, p939_1]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h627, hlam, p939_1]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h0, h4, h627, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p939_1, u1ehi4]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h1, hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [hc13, hlam, hphi, p939_1, u1ehi1]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p939_1, u1ehi3]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p939_1, u1ehi4]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h2, hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [hc14, hlam, hphi, p939_1, u1ehi1]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h932, hlam, p939_1]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h0, h4, h627, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p939_1, u1ehi4]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h3, hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h931, hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h933, hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [h934, hlam, p939_0]
                    · have p939_0 := h939c.1
                      have p939_1 := h939c.2.1
                      have p939_2 := h939c.2.2.1
                      have p939_3 := h939c.2.2.2
                      linarith only [hlam, p939_0]
                  · linarith only [h0, h4, h627, h931, h937, h938, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h627, h937, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
              · linarith only [h7, h931, h936, hc35, hlam, hphi, ht12, ht23, u1ehi4]
            · linarith only [h7, h931, h935, hc34, hlam, hphi, ht12, ht23, u1ehi4]
          · linarith only [h627, h931, h934, hlam]
        · linarith only [h7, h931, h933, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h987 | h987
        · rcases m.htr 1 4 5 (by decide) (by decide) with h988 | h988
          · rcases m.htr 2 3 4 (by decide) (by decide) with h989 | h989
            · linarith only [h7, h932, h989, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h1, h5, h7, h931, h989, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
          · linarith only [h7, h931, h932, h988, hlam]
        · linarith only [h7, h931, h987, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h994 | h994
      · rcases m.htr 1 3 5 (by decide) (by decide) with h995 | h995
        · rcases m.htr 1 4 5 (by decide) (by decide) with h996 | h996
          · rcases m.htr 2 3 4 (by decide) (by decide) with h997 | h997
            · rcases m.htr 2 3 5 (by decide) (by decide) with h998 | h998
              · rcases m.htr 2 4 5 (by decide) (by decide) with h999 | h999
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1000 | h1000
                  · rcases h1bigk with h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c | h1001c
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      rcases p1001_3 (m.d 0 1) (by simp) with h1003 | h1003
                      · rcases p1001_3 (m.d 1 2) (by simp) with h1004 | h1004
                        · linarith only [h1004, hlam, p1001_0]
                        · rcases p1001_3 (m.d 1 3) (by simp) with h1006 | h1006
                          · linarith only [h1, h1006, hlam]
                          · linarith only [h1006, h7, hlam]
                      · linarith only [h1003, hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h1000, h994, hc01, hc45, hlam, hphi, ht0b, ht5b, p1001_1]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      rcases p1001_3 (m.d 0 1) (by simp) with h1011 | h1011
                      · rcases p1001_3 (m.d 1 2) (by simp) with h1012 | h1012
                        · linarith only [h0, h1012, hlam]
                        · rcases p1001_3 (m.d 1 3) (by simp) with h1014 | h1014
                          · linarith only [h1, h1014, hlam]
                          · linarith only [h1014, h994, hlam]
                      · linarith only [h1011, hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      rcases p1001_3 (m.d 0 1) (by simp) with h1018 | h1018
                      · rcases p1001_3 (m.d 1 2) (by simp) with h1019 | h1019
                        · linarith only [h0, h1019, hlam]
                        · rcases p1001_3 (m.d 1 3) (by simp) with h1021 | h1021
                          · linarith only [h1, h1021, hlam]
                          · linarith only [h1021, h995, hlam]
                      · linarith only [h1018, hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h0, hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h7, hlam, p1001_1]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h627, hlam, p1001_1]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h931, hlam, p1001_1]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h1, hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [hc13, hlam, hphi, p1001_1, u1ehi1]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1001_1, u1ehi3]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h1, h931, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1001_1, u1ehi1]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h2, hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [hc14, hlam, hphi, p1001_1, u1ehi1]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h994, hlam, p1001_1]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h0, h4, h627, h931, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1001_1, u1ehi1]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h3, hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [hc15, hlam, hphi, p1001_1, u1ehi1]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h995, hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [h996, hlam, p1001_0]
                    · have p1001_0 := h1001c.1
                      have p1001_1 := h1001c.2.1
                      have p1001_2 := h1001c.2.2.1
                      have p1001_3 := h1001c.2.2.2
                      linarith only [hlam, p1001_0]
                  · rcases h1bigk with h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c | h1045c
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      rcases p1045_3 (m.d 0 1) (by simp) with h1047 | h1047
                      · rcases p1045_3 (m.d 1 2) (by simp) with h1048 | h1048
                        · linarith only [h1048, hlam, p1045_0]
                        · rcases p1045_3 (m.d 1 3) (by simp) with h1050 | h1050
                          · linarith only [h1, h1050, hlam]
                          · linarith only [h1050, h7, hlam]
                      · linarith only [h1047, hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h1000, h994, h996, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1045_1]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h1000, h996, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1045_1]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      rcases p1045_3 (m.d 0 1) (by simp) with h1056 | h1056
                      · rcases p1045_3 (m.d 1 2) (by simp) with h1057 | h1057
                        · linarith only [h0, h1057, hlam]
                        · rcases p1045_3 (m.d 1 3) (by simp) with h1059 | h1059
                          · linarith only [h1, h1059, hlam]
                          · linarith only [h1059, h995, hlam]
                      · linarith only [h1056, hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h0, hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h7, hlam, p1045_1]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h627, hlam, p1045_1]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h931, hlam, p1045_1]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h1, hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [hc13, hlam, hphi, p1045_1, u1ehi1]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h1, h1000, h996, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1045_1]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1045_1, u1ehi4]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h2, hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [hc14, hlam, hphi, p1045_1, u1ehi1]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h994, hlam, p1045_1]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h0, h4, h627, h931, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1045_1, u1ehi1]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h3, hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [hc15, hlam, hphi, p1045_1, u1ehi1]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h995, hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [h996, hlam, p1045_0]
                    · have p1045_0 := h1045c.1
                      have p1045_1 := h1045c.2.1
                      have p1045_2 := h1045c.2.2.1
                      have p1045_3 := h1045c.2.2.2
                      linarith only [hlam, p1045_0]
                · linarith only [h0, h4, h6, h627, h999, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
              · linarith only [h7, h998, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h1, h5, h7, h997, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1086 | h1086
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1087 | h1087
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1088 | h1088
                · linarith only [h1086, h1088, h627, h996, hc23, hlam, hphi, ht12, u1ehi1]
                · linarith only [h1088, h6, h627, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
              · linarith only [h1087, h7, h995, hc13, hlam, hphi, u1ehi1]
            · linarith only [h1086, h7, h994, hc14, hlam, hphi, u1ehi1]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1093 | h1093
          · linarith only [h1093, h994, h995, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1095 | h1095
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1096 | h1096
              · linarith only [h1096, h995, hc23, hlam, hphi, ht12, u1ehi2]
              · linarith only [h1096, h7, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h1095, h7, h994, hc13, hlam, hphi, u1ehi1]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h1100 | h1100
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1101 | h1101
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1102 | h1102
            · linarith only [h1102, h994, hc23, hlam, hphi, ht12, u1ehi2]
            · linarith only [h1, h1102, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · linarith only [h1100, h1101, h994, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h1106 | h1106
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1107 | h1107
            · linarith only [h1107, h7, h994, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h1, h1107, h5, h7, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1110 | h1110
            · linarith only [h1110, h7, h994, hc23, hlam, hphi, ht12, u1ehi1]
            · linarith only [h1110, h7, hc34, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 5590000 in
set_option maxHeartbeats 5590000 in
theorem r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4bigk := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb4 h0 h1 h2 h3 h4 h5 h6 h7
  · exact r1l7_21_14_M_IR_L_I_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb4 h0 h1 h2 h3 h4 h5 h6 h7

end R2N4
