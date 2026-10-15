import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S72
import Jsp000404.R1LeavesN7_0S73

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h41037 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h41038 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h41039 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h42074 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h42254 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 3 4 5 (by decide) (by decide) with h42726 | h42726
  · rcases h1bigk with h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c | h42727c
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h0, hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h33187, hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h36828, hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h39227, hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      rcases p42727_3 (m.d 0 1) (by simp) with h42733 | h42733
      · linarith only [h42733, hlam, p42727_0]
      · rcases p42727_3 (m.d 1 2) (by simp) with h42735 | h42735
        · rcases p42727_3 (m.d 1 3) (by simp) with h42736 | h42736
          · linarith only [h41033, h42736, hlam]
          · linarith only [h33187, h42736, hlam]
        · linarith only [h42735, hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h33187, h41030, h42254, h42726, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p42727_1]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h36828, hc01, hc12, hlam, hphi, p42727_1]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h39227, hc01, hc12, hlam, hphi, p42727_1]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      rcases p42727_3 (m.d 0 1) (by simp) with h42744 | h42744
      · linarith only [h42744, hlam, p42727_0]
      · rcases p42727_3 (m.d 1 2) (by simp) with h42746 | h42746
        · rcases p42727_3 (m.d 1 3) (by simp) with h42747 | h42747
          · rcases p42727_3 (m.d 1 4) (by simp) with h42748 | h42748
            · linarith only [h41036, h42748, hlam]
            · linarith only [h36828, h42748, hlam]
          · linarith only [h42747, hlam, p42727_0]
        · linarith only [h0, h42746, hlam]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h41033, hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h36828, h41030, h41039, h42254, h42726, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42727_1]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h39227, h41033, hc01, hc12, hlam, hphi, p42727_1]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      rcases p42727_3 (m.d 0 1) (by simp) with h42757 | h42757
      · linarith only [h42757, hlam, p42727_0]
      · rcases p42727_3 (m.d 1 2) (by simp) with h42759 | h42759
        · rcases p42727_3 (m.d 1 3) (by simp) with h42760 | h42760
          · rcases p42727_3 (m.d 1 4) (by simp) with h42761 | h42761
            · rcases p42727_3 (m.d 1 5) (by simp) with h42762 | h42762
              · linarith only [h41038, h42762, hlam]
              · linarith only [h39227, h42762, hlam]
            · linarith only [h42761, hlam, p42727_0]
          · linarith only [h33187, h42760, hlam]
        · linarith only [h0, h42759, hlam]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h41034, hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h41036, hlam, p42727_1]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h39227, hc01, hc14, hlam, hphi, p42727_1]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      rcases p42727_3 (m.d 0 1) (by simp) with h42772 | h42772
      · linarith only [h42772, hlam, p42727_0]
      · rcases p42727_3 (m.d 1 2) (by simp) with h42774 | h42774
        · rcases p42727_3 (m.d 1 3) (by simp) with h42775 | h42775
          · rcases p42727_3 (m.d 1 4) (by simp) with h42776 | h42776
            · rcases p42727_3 (m.d 1 5) (by simp) with h42777 | h42777
              · rcases h1emax with h42778 | h42778 | h42778 | h42778 | h42778
                · rcases h2bigk with h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c | h42779c
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h0, hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h41027, h41030, h41039, h42254, h42726, hlam, p42779_2]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h41027, h41030, h42254, h42726, hlam, p42779_2]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    rcases p42779_3 (m.d 0 2) (by simp) with h42784 | h42784
                    · rcases p42779_3 (m.d 1 2) (by simp) with h42785 | h42785
                      · rcases p42779_3 (m.d 2 3) (by simp) with h42786 | h42786
                        · linarith only [h41027, h42786, hlam]
                        · rcases p42779_3 (m.d 2 4) (by simp) with h42788 | h42788
                          · linarith only [h41028, h42788, hlam]
                          · rcases p42779_3 (m.d 2 5) (by simp) with h42790 | h42790
                            · linarith only [h42790, hlam, p42779_0]
                            · rcases h4bigk with h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c | h42792c
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h36828, hlam, p42792_1]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                rcases p42792_3 (m.d 0 4) (by simp) with h42795 | h42795
                                · rcases p42792_3 (m.d 1 4) (by simp) with h42796 | h42796
                                  · rcases p42792_3 (m.d 2 4) (by simp) with h42797 | h42797
                                    · linarith only [h41028, h42797, hlam]
                                    · rcases p42792_3 (m.d 3 4) (by simp) with h42799 | h42799
                                      · linarith only [h41030, h42799, hlam]
                                      · linarith only [h41039, h42799, hlam]
                                  · linarith only [h41034, h42796, hlam]
                                · linarith only [h41028, h42795, hlam]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h41039, h42254, h42726, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42792_1]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                rcases p42792_3 (m.d 0 4) (by simp) with h42805 | h42805
                                · rcases p42792_3 (m.d 1 4) (by simp) with h42806 | h42806
                                  · rcases p42792_3 (m.d 2 4) (by simp) with h42807 | h42807
                                    · linarith only [h41028, h42807, hlam]
                                    · rcases p42792_3 (m.d 3 4) (by simp) with h42809 | h42809
                                      · linarith only [h41030, h42809, hlam]
                                      · linarith only [h42726, h42809, hlam]
                                  · linarith only [h41038, h42806, hlam]
                                · linarith only [h42805, hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h41030, h41033, h41036, h41039, h42254, h42726, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42792_1]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                rcases p42792_3 (m.d 0 4) (by simp) with h42816 | h42816
                                · linarith only [h36828, h42816, hlam]
                                · linarith only [h41028, h42816, hlam]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h41039, h42254, h42726, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42792_1]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                rcases p42792_3 (m.d 0 4) (by simp) with h42820 | h42820
                                · linarith only [h36828, h42820, hlam]
                                · linarith only [h41032, h42820, hlam]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h41028, hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h41034, hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h41039, hlam, p42792_1]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h42254, hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h41030, hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h41036, hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                rcases p42792_3 (m.d 0 4) (by simp) with h42830 | h42830
                                · rcases p42792_3 (m.d 1 4) (by simp) with h42831 | h42831
                                  · rcases p42792_3 (m.d 2 4) (by simp) with h42832 | h42832
                                    · linarith only [h41039, h42832, hlam]
                                    · rcases p42792_3 (m.d 3 4) (by simp) with h42834 | h42834
                                      · rcases p42792_3 (m.d 4 5) (by simp) with h42835 | h42835
                                        · linarith only [h42726, h42835, hlam]
                                        · linarith only [h42254, h42835, hlam]
                                      · linarith only [h41039, h42834, hlam]
                                  · linarith only [h41034, h42831, hlam]
                                · linarith only [h41028, h42830, hlam]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h41027, h41030, h41039, h42254, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42792_1]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h41032, hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h41038, hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h0, h41027, h41030, h41039, h42726, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42792_1]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [h42726, hlam, p42792_0]
                              · have p42792_0 := h42792c.1
                                have p42792_1 := h42792c.2.1
                                have p42792_2 := h42792c.2.2.1
                                have p42792_3 := h42792c.2.2.2
                                linarith only [hlam, p42792_0]
                      · linarith only [h41035, h42785, hlam]
                    · linarith only [h42784, hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h41027, h41030, h41039, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42779_1]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h0, h41027, h41030, h41039, h42254, h42726, hlam, p42779_2]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h0, h41027, h41030, h42254, h42726, hlam, p42779_2]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    rcases p42779_3 (m.d 0 2) (by simp) with h42854 | h42854
                    · linarith only [h0, h42854, hlam]
                    · linarith only [h41029, h42854, hlam]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h41027, hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h41033, hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h41039, hlam, p42779_1]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h42074, hlam, p42779_1]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h41028, hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h41034, hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h0, h41027, h41030, h42254, h42726, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42779_1]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h42254, hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h41029, hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h41035, hlam, p42779_0]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h0, h41027, h41030, h42254, h42726, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42779_1]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [h0, h41027, h41030, h42254, h42726, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p42779_1]
                  · have p42779_0 := h42779c.1
                    have p42779_1 := h42779c.2.1
                    have p42779_2 := h42779c.2.2.1
                    have p42779_3 := h42779c.2.2.2
                    linarith only [hlam, p42779_0]
                · linarith only [h0, h41027, h41030, h42254, h42726, h42778, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h33187, h41030, h41039, h42254, h42726, h42778, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h41038, h42778, hc01, hlam, p42727_1]
                · linarith only [h42778, hc01, hlam, p42727_1]
              · linarith only [h42777, hlam, p42727_0]
            · linarith only [h36828, h42776, hlam]
          · linarith only [h33187, h42775, hlam]
        · linarith only [h0, h42774, hlam]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h41035, hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h41037, hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [h41038, hlam, p42727_0]
    · have p42727_0 := h42727c.1
      have p42727_1 := h42727c.2.1
      have p42727_2 := h42727c.2.2.1
      have p42727_3 := h42727c.2.2.2
      linarith only [hlam, p42727_0]
  · rcases h1bigk with h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c | h42884c
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h0, hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h33187, hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h36828, hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h39227, hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      rcases p42884_3 (m.d 0 1) (by simp) with h42890 | h42890
      · linarith only [h42890, hlam, p42884_0]
      · rcases p42884_3 (m.d 1 2) (by simp) with h42892 | h42892
        · rcases p42884_3 (m.d 1 3) (by simp) with h42893 | h42893
          · linarith only [h41033, h42893, hlam]
          · linarith only [h33187, h42893, hlam]
        · linarith only [h42892, hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h33187, hc01, hc12, hlam, hphi, p42884_1]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h36828, hc01, hc12, hlam, hphi, p42884_1]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h39227, hc01, hc12, hlam, hphi, p42884_1]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      rcases p42884_3 (m.d 0 1) (by simp) with h42901 | h42901
      · linarith only [h42901, hlam, p42884_0]
      · rcases p42884_3 (m.d 1 2) (by simp) with h42903 | h42903
        · rcases p42884_3 (m.d 1 3) (by simp) with h42904 | h42904
          · rcases p42884_3 (m.d 1 4) (by simp) with h42905 | h42905
            · linarith only [h41036, h42905, hlam]
            · linarith only [h36828, h42905, hlam]
          · linarith only [h42904, hlam, p42884_0]
        · linarith only [h0, h42903, hlam]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h41033, hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h36828, h41032, h42726, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p42884_1]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h39227, h41033, hc01, hc12, hlam, hphi, p42884_1]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      rcases p42884_3 (m.d 0 1) (by simp) with h42914 | h42914
      · linarith only [h42914, hlam, p42884_0]
      · rcases p42884_3 (m.d 1 2) (by simp) with h42916 | h42916
        · rcases p42884_3 (m.d 1 3) (by simp) with h42917 | h42917
          · rcases p42884_3 (m.d 1 4) (by simp) with h42918 | h42918
            · rcases p42884_3 (m.d 1 5) (by simp) with h42919 | h42919
              · linarith only [h41038, h42919, hlam]
              · linarith only [h39227, h42919, hlam]
            · linarith only [h42918, hlam, p42884_0]
          · linarith only [h33187, h42917, hlam]
        · linarith only [h0, h42916, hlam]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h41034, hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h41036, hlam, p42884_1]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h39227, h41032, h41039, h42726, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42884_1]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      rcases p42884_3 (m.d 0 1) (by simp) with h42929 | h42929
      · linarith only [h42929, hlam, p42884_0]
      · rcases p42884_3 (m.d 1 2) (by simp) with h42931 | h42931
        · rcases p42884_3 (m.d 1 3) (by simp) with h42932 | h42932
          · rcases p42884_3 (m.d 1 4) (by simp) with h42933 | h42933
            · rcases p42884_3 (m.d 1 5) (by simp) with h42934 | h42934
              · rcases h1emax with h42935 | h42935 | h42935 | h42935 | h42935
                · rcases h2bigk with h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c | h42936c
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h0, hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h41028, h41032, h41039, h42726, hlam, p42936_2]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    rcases p42936_3 (m.d 0 2) (by simp) with h42940 | h42940
                    · rcases p42936_3 (m.d 1 2) (by simp) with h42941 | h42941
                      · rcases p42936_3 (m.d 2 3) (by simp) with h42942 | h42942
                        · linarith only [h41027, h42942, hlam]
                        · rcases p42936_3 (m.d 2 4) (by simp) with h42944 | h42944
                          · linarith only [h42944, hlam, p42936_0]
                          · rcases p42936_3 (m.d 2 5) (by simp) with h42946 | h42946
                            · linarith only [h41029, h42946, hlam]
                            · linarith only [h42254, h42946, hlam]
                      · linarith only [h41034, h42941, hlam]
                    · linarith only [h42940, hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    rcases p42936_3 (m.d 0 2) (by simp) with h42951 | h42951
                    · rcases p42936_3 (m.d 1 2) (by simp) with h42952 | h42952
                      · rcases p42936_3 (m.d 2 3) (by simp) with h42953 | h42953
                        · linarith only [h41027, h42953, hlam]
                        · rcases p42936_3 (m.d 2 4) (by simp) with h42955 | h42955
                          · linarith only [h41028, h42955, hlam]
                          · rcases p42936_3 (m.d 2 5) (by simp) with h42957 | h42957
                            · linarith only [h42957, hlam, p42936_0]
                            · rcases h4bigk with h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c | h42959c
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h36828, hlam, p42959_1]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                rcases p42959_3 (m.d 0 4) (by simp) with h42962 | h42962
                                · rcases p42959_3 (m.d 1 4) (by simp) with h42963 | h42963
                                  · rcases p42959_3 (m.d 2 4) (by simp) with h42964 | h42964
                                    · linarith only [h41028, h42964, hlam]
                                    · rcases p42959_3 (m.d 3 4) (by simp) with h42966 | h42966
                                      · linarith only [h41030, h42966, hlam]
                                      · linarith only [h41039, h42966, hlam]
                                  · linarith only [h41034, h42963, hlam]
                                · linarith only [h41028, h42962, hlam]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                rcases p42959_3 (m.d 0 4) (by simp) with h42971 | h42971
                                · rcases p42959_3 (m.d 1 4) (by simp) with h42972 | h42972
                                  · rcases p42959_3 (m.d 2 4) (by simp) with h42973 | h42973
                                    · linarith only [h41028, h42973, hlam]
                                    · rcases p42959_3 (m.d 3 4) (by simp) with h42975 | h42975
                                      · linarith only [h41030, h42975, hlam]
                                      · rcases p42959_3 (m.d 4 5) (by simp) with h42977 | h42977
                                        · linarith only [h41032, h42977, hlam]
                                        · linarith only [h42726, h42977, hlam]
                                  · linarith only [h41036, h42972, hlam]
                                · linarith only [h41030, h42971, hlam]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h41027, h41030, h41039, h42726, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42959_1]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h41032, h41033, h41036, h41039, h42726, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42959_1]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                rcases p42959_3 (m.d 0 4) (by simp) with h42985 | h42985
                                · linarith only [h36828, h42985, hlam]
                                · linarith only [h41028, h42985, hlam]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                rcases p42959_3 (m.d 0 4) (by simp) with h42988 | h42988
                                · linarith only [h36828, h42988, hlam]
                                · linarith only [h41030, h42988, hlam]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h41033, h41036, h41039, h42726, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42959_1]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h41028, hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h41034, hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h41039, hlam, p42959_1]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h42254, hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h41030, hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h41036, hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h41032, h42726, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p42959_1]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h42726, hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h41032, hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h41038, hlam, p42959_0]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                rcases p42959_3 (m.d 0 4) (by simp) with h43004 | h43004
                                · rcases p42959_3 (m.d 1 4) (by simp) with h43005 | h43005
                                  · rcases p42959_3 (m.d 2 4) (by simp) with h43006 | h43006
                                    · linarith only [h43006, hlam, p42959_0]
                                    · rcases p42959_3 (m.d 3 4) (by simp) with h43008 | h43008
                                      · linarith only [h42726, h43008, hlam]
                                      · linarith only [h41039, h43008, hlam]
                                  · linarith only [h41034, h43005, hlam]
                                · linarith only [h41028, h43004, hlam]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [h36828, h41032, h41033, h41036, h41039, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42959_1]
                              · have p42959_0 := h42959c.1
                                have p42959_1 := h42959c.2.1
                                have p42959_2 := h42959c.2.2.1
                                have p42959_3 := h42959c.2.2.2
                                linarith only [hlam, p42959_0]
                      · linarith only [h41035, h42952, hlam]
                    · linarith only [h42951, hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h41027, h41030, h41039, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42936_1]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h0, h41027, h41030, h41032, h41039, h42726, hlam, p42936_2]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    rcases p42936_3 (m.d 0 2) (by simp) with h43020 | h43020
                    · linarith only [h0, h43020, hlam]
                    · linarith only [h41028, h43020, hlam]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    rcases p42936_3 (m.d 0 2) (by simp) with h43023 | h43023
                    · linarith only [h0, h43023, hlam]
                    · linarith only [h41029, h43023, hlam]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h41027, hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h41033, hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h41039, hlam, p42936_1]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h42074, hlam, p42936_1]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h41028, hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h41034, hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h41027, h41030, h41032, h41039, h42726, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p42936_1]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h42254, hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h41029, hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [h41035, hlam, p42936_0]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    rcases p42936_3 (m.d 0 2) (by simp) with h43038 | h43038
                    · rcases p42936_3 (m.d 1 2) (by simp) with h43039 | h43039
                      · rcases p42936_3 (m.d 2 3) (by simp) with h43040 | h43040
                        · linarith only [h42074, h43040, hlam]
                        · rcases p42936_3 (m.d 2 4) (by simp) with h43042 | h43042
                          · linarith only [h42254, h43042, hlam]
                          · linarith only [h41039, h43042, hlam]
                      · linarith only [h41033, h43039, hlam]
                    · linarith only [h41027, h43038, hlam]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    rcases p42936_3 (m.d 0 2) (by simp) with h43047 | h43047
                    · rcases p42936_3 (m.d 1 2) (by simp) with h43048 | h43048
                      · rcases p42936_3 (m.d 2 3) (by simp) with h43049 | h43049
                        · linarith only [h42074, h43049, hlam]
                        · rcases p42936_3 (m.d 2 4) (by simp) with h43051 | h43051
                          · linarith only [h42254, h43051, hlam]
                          · rcases p42936_3 (m.d 2 5) (by simp) with h43053 | h43053
                            · rcases h4bigk with h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c | h43054c
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h36828, hlam, p43054_1]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h41032, h42254, hlam, p42936_1, p43054_2]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                rcases p43054_3 (m.d 0 4) (by simp) with h43058 | h43058
                                · rcases p43054_3 (m.d 1 4) (by simp) with h43059 | h43059
                                  · rcases p43054_3 (m.d 2 4) (by simp) with h43060 | h43060
                                    · linarith only [h41028, h43060, hlam]
                                    · rcases p43054_3 (m.d 3 4) (by simp) with h43062 | h43062
                                      · linarith only [h41030, h43062, hlam]
                                      · rcases p43054_3 (m.d 4 5) (by simp) with h43064 | h43064
                                        · linarith only [h41032, h43064, hlam]
                                        · linarith only [h42726, h43064, hlam]
                                  · linarith only [h41036, h43059, hlam]
                                · linarith only [h41030, h43058, hlam]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h36828, h41033, h41036, h42074, h42726, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p42936_1, p43054_1]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h41032, h41033, h41036, h42074, h42726, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p42936_1, p43054_1]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h36828, h41032, h42074, h42726, hlam, p42936_1, p43054_2]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                rcases p43054_3 (m.d 0 4) (by simp) with h43073 | h43073
                                · linarith only [h36828, h43073, hlam]
                                · linarith only [h41030, h43073, hlam]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h41039, h42074, h42726, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p42936_1, p43054_1]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h41028, hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h41034, hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h41039, hlam, p43054_1]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h42254, hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h41030, hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h41036, hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h41032, h41039, h42726, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p43054_1]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h42726, hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h41032, hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h41038, hlam, p43054_0]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                rcases p43054_3 (m.d 0 4) (by simp) with h43089 | h43089
                                · rcases p43054_3 (m.d 1 4) (by simp) with h43090 | h43090
                                  · rcases p43054_3 (m.d 2 4) (by simp) with h43091 | h43091
                                    · linarith only [h43091, hlam, p43054_0]
                                    · rcases p43054_3 (m.d 3 4) (by simp) with h43093 | h43093
                                      · linarith only [h42726, h43093, hlam]
                                      · linarith only [h41039, h43093, hlam]
                                  · linarith only [h41034, h43090, hlam]
                                · linarith only [h41028, h43089, hlam]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [h36828, h41032, h41033, h41036, h41039, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p43054_1]
                              · have p43054_0 := h43054c.1
                                have p43054_1 := h43054c.2.1
                                have p43054_2 := h43054c.2.2.1
                                have p43054_3 := h43054c.2.2.2
                                linarith only [hlam, p43054_0]
                            · linarith only [h42254, h43053, hlam]
                      · linarith only [h41034, h43048, hlam]
                    · linarith only [h41028, h43047, hlam]
                  · have p42936_0 := h42936c.1
                    have p42936_1 := h42936c.2.1
                    have p42936_2 := h42936c.2.2.1
                    have p42936_3 := h42936c.2.2.2
                    linarith only [hlam, p42936_0]
                · linarith only [h0, h42935, hc01, hlam]
                · linarith only [h33187, h41030, h41032, h41039, h42726, h42935, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h36828, h41032, h41039, h42726, h42935, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h42935, hc01, hlam, p42884_1]
              · linarith only [h42934, hlam, p42884_0]
            · linarith only [h36828, h42933, hlam]
          · linarith only [h33187, h42932, hlam]
        · linarith only [h0, h42931, hlam]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h41035, hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h41037, hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [h41038, hlam, p42884_0]
    · have p42884_0 := h42884c.1
      have p42884_1 := h42884c.2.1
      have p42884_2 := h42884c.2.2.1
      have p42884_3 := h42884c.2.2.2
      linarith only [hlam, p42884_0]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h41037 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h41038 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h41039 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h42074 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 2 4 5 (by decide) (by decide) with h42254 | h42254
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037 h41038 h41039 h42074 h42254
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037 h41038 h41039 h42074 h42254

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h41037 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h41038 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h41039 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 2 3 5 (by decide) (by decide) with h42074 | h42074
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037 h41038 h41039 h42074
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037 h41038 h41039 h42074

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h41037 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h41038 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 2 3 4 (by decide) (by decide) with h41039 | h41039
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037 h41038 h41039
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037 h41038 h41039

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h41037 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h41038 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  linarith only [h36828, h41032, h41038, hlam]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h41037 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 1 4 5 (by decide) (by decide) with h41038 | h41038
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037 h41038
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037 h41038

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h41037 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  linarith only [h33187, h41031, h41037, hlam]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 1 3 5 (by decide) (by decide) with h41037 | h41037
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036 h41037

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h41036 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  linarith only [h33187, h41030, h41036, hlam]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 1 3 4 (by decide) (by decide) with h41036 | h41036
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035 h41036

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h41035 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  linarith only [h0, h41029, h41035, hlam]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 1 2 5 (by decide) (by decide) with h41035 | h41035
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034 h41035

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h41034 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  linarith only [h0, h41028, h41034, hlam]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 1 2 4 (by decide) (by decide) with h41034 | h41034
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033 h41034

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h41033 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  linarith only [h0, h41027, h41033, hlam]

set_option maxHeartbeats 5882000 in
set_option maxHeartbeats 5882000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg41027 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg41028 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg41029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg41030 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg41031 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h41032 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  have h41027 := hg41027
  have h41028 := hg41028
  have h41029 := hg41029
  have h41030 := hg41030
  have h41031 := hg41031
  rcases m.htr 1 2 3 (by decide) (by decide) with h41033 | h41033
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s44_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 hg39227 hg41027 hg41028 hg41029 hg41030 hg41031 h41032 h41033

end R2N4
