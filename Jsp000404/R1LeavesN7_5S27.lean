import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S24
import Jsp000404.R1LeavesN7_5S25
import Jsp000404.R1LeavesN7_5S26

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10516000 in
set_option maxHeartbeats 10516000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11844 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h15274 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15741 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h15990 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h15991 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  rcases m.htr 0 4 5 (by decide) (by decide) with h16716 | h16716
  · linarith only [h15990, h15991, h16716, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h16718 | h16718
    · rcases m.htr 1 2 4 (by decide) (by decide) with h16719 | h16719
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16720 | h16720
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16721 | h16721
          · rcases m.htr 1 3 5 (by decide) (by decide) with h16722 | h16722
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16723 | h16723
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16724 | h16724
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16725 | h16725
                  · linarith only [h15990, h15991, h16718, h16725, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h11844, h16718, h16722, h16725, hc01, hc12, hlam, hphi]
                · linarith only [h0, h11844, h15990, h16724, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16729 | h16729
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16730 | h16730
                  · linarith only [h15990, h15991, h16718, h16730, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h11844, h16718, h16722, h16730, hc01, hc12, hlam, hphi]
                · linarith only [h0, h11844, h15990, h15991, h16718, h16722, h16729, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16734 | h16734
              · linarith only [h16716, h16721, h16722, h16734, h9935, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16736 | h16736
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16737 | h16737
                  · linarith only [h16718, h16722, h16737, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16739 | h16739
                    · linarith only [h16719, h16734, h16739, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16741 | h16741
                      · linarith only [h15990, h16734, h16741, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · rcases h0bigk with h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c | h16743c
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [hlam, p16743_0]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h0, hlam, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h6310, hlam, p16743_0]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h9935, hlam, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h11282, hlam, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h11844, h16718, h16722, h16741, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [hlam, p16743_0]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h11844, hlam, p16743_0]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h15274, hlam, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h15741, hlam, p16743_0]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h11844, h16718, h16722, h16741, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h11844, h16718, h16722, h16741, hc02, hc45, hlam, hphi, ht23, ht34, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [hlam, p16743_0]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h11844, h16718, h16722, h16741, hc04, hc45, hlam, hphi, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h15991, hlam, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h16721, h16722, h16741, h9935, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h0, h16721, h16722, h16741, h9935, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h15990, hlam, p16743_0]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [hlam, p16743_0]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h16716, hlam, p16743_0]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h15741, h16720, hc01, hc12, hlam, hphi, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h0, h15741, h16720, hc01, hc12, hlam, hphi, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h15741, h15990, h16720, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [h15741, h16720, h9935, hc01, hc12, hlam, hphi, p16743_1]
                        · have p16743_0 := h16743c.1
                          have p16743_1 := h16743c.2.1
                          have p16743_2 := h16743c.2.2.1
                          have p16743_3 := h16743c.2.2.2
                          linarith only [hlam, p16743_0]
                · linarith only [h0, h11844, h15990, h16736, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
          · linarith only [h11844, h15990, h16718, h16721, hlam]
        · linarith only [h0, h11844, h16718, h16720, hc01, hc25, hlam, hphi, ht12]
      · linarith only [h0, h11844, h16718, h16719, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h16773 | h16773
      · linarith only [h0, h15274, h16718, h16773, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16775 | h16775
        · linarith only [h0, h15741, h16718, h16775, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16777 | h16777
          · rcases m.htr 1 3 5 (by decide) (by decide) with h16778 | h16778
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16779 | h16779
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16780 | h16780
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16781 | h16781
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16782 | h16782
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16783 | h16783
                      · linarith only [h0, h15274, h15990, h16716, h16783, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases h0bigk with h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c | h16785c
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [hlam, p16785_0]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h0, hlam, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h6310, hlam, p16785_0]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h9935, hlam, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h11282, hlam, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h0, h16775, h16780, h16782, hc01, hc23, hlam, hphi, ht12, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [hlam, p16785_0]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h11844, hlam, p16785_0]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h15274, hlam, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h15741, hlam, p16785_0]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h15991, h16773, h16779, h16780, h16783, hc01, hc23, hlam, hphi, ht12, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h15991, h16773, h16779, h16780, h16783, hc02, hc23, hlam, hphi, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [hlam, p16785_0]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h0, h15274, h15991, h16773, h16779, h16780, h16783, hc01, hc23, hlam, hphi, ht12, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h15991, hlam, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h15990, h15991, h16773, h16779, h16780, h16783, hc01, hc23, hlam, hphi, ht12, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h0, h15990, h15991, h16773, h16779, h16780, h16783, hc01, hc23, hlam, hphi, ht12, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h15990, hlam, p16785_0]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [hlam, p16785_0]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h16716, hlam, p16785_0]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h15991, h16773, h16779, h16780, h16783, hc01, hc23, hlam, hphi, ht12, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h0, h15991, h16773, h16779, h16780, h16783, hc01, hc23, hlam, hphi, ht12, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h15990, h15991, h16773, h16779, h16780, h16783, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [h15991, h16773, h16779, h16780, h16783, h9935, hc01, hc23, hlam, hphi, ht12, p16785_1]
                        · have p16785_0 := h16785c.1
                          have p16785_1 := h16785c.2.1
                          have p16785_2 := h16785c.2.2.1
                          have p16785_3 := h16785c.2.2.2
                          linarith only [hlam, p16785_0]
                    · linarith only [h16773, h16779, h16782, hlam]
                  · linarith only [h0, h15274, h16716, h16773, h16779, h16780, h16781, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h15274, h15990, h16716, h16718, h16777, h16779, h16780, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16814 | h16814
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16815 | h16815
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16816 | h16816
                    · linarith only [h16779, h16816, h9935, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h16773, h16816, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h16718, h16778, h16815, hlam]
                · linarith only [h15990, h15991, h16718, h16778, h16814, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16821 | h16821
              · linarith only [h0, h15274, h16716, h16777, h16778, h16821, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16823 | h16823
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16824 | h16824
                  · linarith only [h16778, h16824, h6310, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h16718, h16824, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h15990, h16718, h16823, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
          · linarith only [h15990, h16777, h6310, hlam]

set_option maxHeartbeats 10516000 in
set_option maxHeartbeats 10516000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11844 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h15274 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15741 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h15990 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  rcases m.htr 0 3 5 (by decide) (by decide) with h15991 | h15991
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x1_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 h11844 h15274 h15741 h15990 h15991
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x1_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 h11844 h15274 h15741 h15990 h15991

set_option maxHeartbeats 10516000 in
set_option maxHeartbeats 10516000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11844 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h15274 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15741 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h15990 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  rcases m.htr 0 3 5 (by decide) (by decide) with h16829 | h16829
  · rcases m.htr 0 4 5 (by decide) (by decide) with h16830 | h16830
    · rcases m.htr 1 2 3 (by decide) (by decide) with h16831 | h16831
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16832 | h16832
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16833 | h16833
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16834 | h16834
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16835 | h16835
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16836 | h16836
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16837 | h16837
                  · linarith only [h0, h15741, h15990, h16829, h16831, h16837, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11844, h16834, h16837, hc01, hc13, hlam, hphi]
                · linarith only [h15741, h16830, h16833, h16836, h9935, hc01, hc12, hlam, hphi]
              · linarith only [h15990, h16834, h16835, hc03, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16842 | h16842
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16843 | h16843
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16844 | h16844
                  · linarith only [h16831, h16834, h16844, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16846 | h16846
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16847 | h16847
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16848 | h16848
                        · rcases h0bigk with h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c | h16849c
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [hlam, p16849_0]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h0, hlam, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h6310, hlam, p16849_0]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h9935, hlam, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h11282, hlam, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h15741, h16833, hc01, hc15, hlam, hphi, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [hlam, p16849_0]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h11844, hlam, p16849_0]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h15274, hlam, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h15741, hlam, p16849_0]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h16834, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h16834, h6310, hc02, hc34, hlam, hphi, ht23, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [hlam, p16849_0]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h15990, hlam, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h11282, h16834, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h15274, h16832, hc01, hc12, hlam, hphi, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h0, h15274, h16832, hc01, hc12, hlam, hphi, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h15274, h16829, h16832, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [hlam, p16849_0]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h0, h15274, h15741, h16832, hc01, hc12, hlam, hphi, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h15741, h16831, h16834, h16846, hc01, hc34, hlam, hphi, ht12, ht23, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h0, h15741, h16831, h16834, h16846, hc01, hc34, hlam, hphi, ht12, ht23, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h16829, hlam, p16849_0]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [h16830, hlam, p16849_1]
                          · have p16849_0 := h16849c.1
                            have p16849_1 := h16849c.2.1
                            have p16849_2 := h16849c.2.2.1
                            have p16849_3 := h16849c.2.2.2
                            linarith only [hlam, p16849_0]
                        · linarith only [h16834, h16848, h6310, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h15274, h16830, h16847, hlam]
                    · linarith only [h16829, h16834, h16846, h6310, hc23, hc34, hlam, hphi]
                · linarith only [h15274, h16830, h16832, h16843, hlam]
              · linarith only [h11844, h16829, h16831, h16842, hlam]
          · linarith only [h0, h15274, h16832, h16833, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11844, h16831, h16832, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16882 | h16882
        · linarith only [h0, h15274, h16831, h16882, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16884 | h16884
          · linarith only [h0, h15741, h16831, h16884, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16886 | h16886
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16887 | h16887
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16888 | h16888
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16889 | h16889
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16890 | h16890
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16891 | h16891
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16892 | h16892
                        · rcases h0bigk with h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c | h16893c
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [hlam, p16893_0]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h0, hlam, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h6310, hlam, p16893_0]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h9935, hlam, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h11282, hlam, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h0, h16884, h16889, h16891, hc01, hc23, hlam, hphi, ht12, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [hlam, p16893_0]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h11844, hlam, p16893_0]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h15274, hlam, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h15741, hlam, p16893_0]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h15990, h16831, h16886, hc01, hc23, hlam, hphi, ht12, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h0, h15990, h16831, h16886, hc01, hc23, hlam, hphi, ht12, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [hlam, p16893_0]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h15990, hlam, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h0, h15741, h15990, h16831, h16886, hc01, hc23, hlam, hphi, ht12, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h15990, h16831, h16886, hc01, hc23, hlam, hphi, ht12, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h0, h15990, h16831, h16886, hc01, hc23, hlam, hphi, ht12, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h15990, h16829, h16831, h16886, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [hlam, p16893_0]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h0, h15741, h15990, h16831, h16886, hc01, hc23, hlam, hphi, ht12, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h15990, h16829, h16831, h16886, hc01, hc23, hlam, hphi, ht12, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h0, h15990, h16829, h16831, h16886, hc01, hc23, hlam, hphi, ht12, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h16829, hlam, p16893_0]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [h16830, hlam, p16893_1]
                          · have p16893_0 := h16893c.1
                            have p16893_1 := h16893c.2.1
                            have p16893_2 := h16893c.2.2.1
                            have p16893_3 := h16893c.2.2.2
                            linarith only [hlam, p16893_0]
                        · linarith only [h15990, h16830, h16892, hlam]
                      · linarith only [h0, h15274, h15990, h16829, h16830, h16886, h16891, hc01, hc14, hlam, hphi]
                    · linarith only [h15990, h16831, h16886, h16890, hc03, hc35, hlam, hphi]
                  · linarith only [h16831, h16886, h16889, hlam]
                · linarith only [h15990, h16829, h16830, h16886, h16888, h9935, hc01, hc13, hlam, hphi]
              · linarith only [h15990, h16829, h16886, h16887, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16925 | h16925
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16926 | h16926
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16927 | h16927
                  · linarith only [h0, h16884, h16886, h16925, h16927, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h16831, h16927, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h15990, h16829, h16830, h16926, h9935, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h16829, h16925, h6310, hlam]
    · linarith only [h15990, h16829, h16830, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h16933 | h16933
    · rcases m.htr 1 2 3 (by decide) (by decide) with h16934 | h16934
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16935 | h16935
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16936 | h16936
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16937 | h16937
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16938 | h16938
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16939 | h16939
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16940 | h16940
                  · linarith only [h0, h11844, h15990, h16934, h16940, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11844, h16934, h16937, h16940, hc01, hc12, hlam, hphi]
                · linarith only [h15990, h16933, h16934, h16937, h16939, h9935, hc01, hc12, hlam, hphi]
              · linarith only [h15990, h16937, h16938, hc03, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16945 | h16945
              · linarith only [h0, h11844, h16829, h16937, h16945, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16947 | h16947
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16948 | h16948
                  · linarith only [h16937, h16948, h6310, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16950 | h16950
                    · linarith only [h0, h11844, h16829, h16934, h16937, h16950, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16952 | h16952
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16953 | h16953
                        · rcases h0bigk with h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c | h16954c
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [hlam, p16954_0]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h0, hlam, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h6310, hlam, p16954_0]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h9935, hlam, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h11282, hlam, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h11844, h16945, h16953, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [hlam, p16954_0]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h11844, hlam, p16954_0]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h15274, hlam, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h15741, hlam, p16954_0]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h16945, h16953, h6310, hc01, hc34, hlam, hphi, ht12, ht23, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h16945, h16953, h6310, hc02, hc34, hlam, hphi, ht23, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [hlam, p16954_0]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h15990, hlam, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h16829, hlam, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h15274, h16935, hc01, hc12, hlam, hphi, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h0, h15274, h16935, hc01, hc12, hlam, hphi, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h15274, h16935, h6310, hc01, hc12, hlam, hphi, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [hlam, p16954_0]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h11282, h15274, h16935, hc01, hc12, hlam, hphi, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h15274, h16933, h16935, hc01, hc12, hlam, hphi, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h0, h15274, h16933, h16935, hc01, hc12, hlam, hphi, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h0, h11844, h15274, h16933, h16935, hc01, hc12, hlam, hphi, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [h16933, hlam, p16954_1]
                          · have p16954_0 := h16954c.1
                            have p16954_1 := h16954c.2.1
                            have p16954_2 := h16954c.2.2.1
                            have p16954_3 := h16954c.2.2.2
                            linarith only [hlam, p16954_0]
                        · linarith only [h0, h11844, h15274, h15990, h16933, h16935, h16953, hc01, hc12, hlam, hphi]
                      · linarith only [h15274, h16933, h16952, hlam]
                · linarith only [h15274, h16933, h16935, h16947, hlam]
          · linarith only [h0, h15274, h16935, h16936, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11844, h16934, h16935, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16985 | h16985
        · linarith only [h0, h15274, h16934, h16985, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16987 | h16987
          · linarith only [h0, h15741, h16934, h16987, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16989 | h16989
            · rcases m.htr 1 3 5 (by decide) (by decide) with h16990 | h16990
              · rcases m.htr 1 4 5 (by decide) (by decide) with h16991 | h16991
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16992 | h16992
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16993 | h16993
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h16994 | h16994
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16995 | h16995
                        · rcases h0bigk with h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c | h16996c
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [hlam, p16996_0]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h0, hlam, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h6310, hlam, p16996_0]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h9935, hlam, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h11282, hlam, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h11844, h16829, h16989, h16995, hc01, hc13, hlam, hphi, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [hlam, p16996_0]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h11844, hlam, p16996_0]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h15274, hlam, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h15741, hlam, p16996_0]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h16829, h16989, h16995, hc01, hc13, hlam, hphi, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h16829, h16989, h16995, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [hlam, p16996_0]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h15990, hlam, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h16829, hlam, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h15990, h16989, hc01, hc13, hlam, hphi, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h0, h15990, h16989, hc01, hc13, hlam, hphi, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h15990, h16989, h6310, hc01, hc13, hlam, hphi, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [hlam, p16996_0]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h0, h11844, h15990, h16829, h16989, hc01, hc13, hlam, hphi, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h16829, h16989, h16995, hc01, hc13, hlam, hphi, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h0, h16829, h16989, h16995, hc01, hc13, hlam, hphi, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h0, h11844, h16829, h16989, h16995, hc01, hc13, hlam, hphi, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [h16933, hlam, p16996_1]
                          · have p16996_0 := h16996c.1
                            have p16996_1 := h16996c.2.1
                            have p16996_2 := h16996c.2.2.1
                            have p16996_3 := h16996c.2.2.2
                            linarith only [hlam, p16996_0]
                        · linarith only [h15990, h16933, h16995, hlam]
                      · linarith only [h0, h15274, h16933, h16994, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h11844, h15990, h16934, h16989, h16993, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h16934, h16989, h16992, hlam]
                · linarith only [h15990, h16933, h16989, h16991, hlam]
              · linarith only [h0, h11844, h15990, h16989, h16990, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h17028 | h17028
              · linarith only [h0, h11844, h16829, h16989, h17028, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h17030 | h17030
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17031 | h17031
                  · linarith only [h16989, h17031, h6310, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h16934, h17031, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h16933, h17030, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h17035 | h17035
      · rcases m.htr 1 2 4 (by decide) (by decide) with h17036 | h17036
        · rcases m.htr 1 2 5 (by decide) (by decide) with h17037 | h17037
          · rcases m.htr 1 3 4 (by decide) (by decide) with h17038 | h17038
            · rcases m.htr 1 3 5 (by decide) (by decide) with h17039 | h17039
              · rcases m.htr 1 4 5 (by decide) (by decide) with h17040 | h17040
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17041 | h17041
                  · linarith only [h0, h11844, h15990, h17035, h17041, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11844, h17038, h17041, hc01, hc13, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17044 | h17044
                  · linarith only [h0, h11844, h15990, h17035, h17044, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h11844, h17038, h17040, h17044, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h11844, h15990, h17038, h17039, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h17048 | h17048
              · linarith only [h0, h11844, h16829, h17038, h17048, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h17050 | h17050
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17051 | h17051
                  · linarith only [h17038, h17051, h6310, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h17053 | h17053
                    · linarith only [h17035, h17048, h17053, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h17055 | h17055
                      · linarith only [h0, h11844, h15990, h16933, h17036, h17055, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h15274, h17050, h17055, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17058 | h17058
                  · linarith only [h0, h11844, h15990, h17035, h17048, h17058, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h17060 | h17060
                    · linarith only [h0, h11844, h16829, h17035, h17060, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h17062 | h17062
                      · linarith only [h17038, h17050, h17062, h6310, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h17064 | h17064
                        · linarith only [h0, h11844, h17035, h17038, h17050, h17064, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h11844, h17035, h17038, h17064, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h11844, h17035, h17037, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11844, h17035, h17036, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h17069 | h17069
        · linarith only [h0, h15274, h17035, h17069, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h17071 | h17071
          · linarith only [h0, h15741, h17035, h17071, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h17073 | h17073
            · rcases m.htr 1 3 5 (by decide) (by decide) with h17074 | h17074
              · rcases m.htr 1 4 5 (by decide) (by decide) with h17075 | h17075
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17076 | h17076
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h17077 | h17077
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h17078 | h17078
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h17079 | h17079
                        · linarith only [h0, h11844, h15990, h16933, h17035, h17073, h17079, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h11844, h15990, h17075, h17079, hc01, hc14, hlam, hphi]
                      · linarith only [h17069, h17075, h17078, hlam]
                    · linarith only [h0, h11844, h15990, h16933, h17069, h17075, h17076, h17077, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h11844, h15990, h16933, h17035, h17073, h17075, h17076, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17085 | h17085
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h17086 | h17086
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h17087 | h17087
                      · linarith only [h0, h11844, h15990, h17073, h17075, h17087, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h0, h17069, h17087, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h17035, h17074, h17086, hlam]
                  · linarith only [h17035, h17073, h17085, hlam]
              · linarith only [h0, h11844, h15990, h17073, h17074, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h17093 | h17093
              · linarith only [h0, h11844, h16829, h17073, h17093, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h17095 | h17095
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17096 | h17096
                  · linarith only [h17073, h17096, h6310, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h17035, h17096, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h17099 | h17099
                  · linarith only [h0, h17035, h17073, h17099, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h17035, h17099, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 10516000 in
set_option maxHeartbeats 10516000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11844 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h15274 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15741 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  rcases m.htr 0 3 4 (by decide) (by decide) with h15990 | h15990
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 h11844 h15274 h15741 h15990
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 h11844 h15274 h15741 h15990

set_option maxHeartbeats 10516000 in
set_option maxHeartbeats 10516000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11844 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h15274 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  rcases m.htr 0 2 5 (by decide) (by decide) with h15741 | h15741
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 h11844 h15274 h15741
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 h11844 h15274 h15741

set_option maxHeartbeats 10516000 in
set_option maxHeartbeats 10516000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11844 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  rcases m.htr 0 2 4 (by decide) (by decide) with h15274 | h15274
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 h11844 h15274
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 h11844 h15274

set_option maxHeartbeats 10516000 in
set_option maxHeartbeats 10516000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  rcases m.htr 0 2 3 (by decide) (by decide) with h11844 | h11844
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 h11844
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s16_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 h11844

end R2N4
